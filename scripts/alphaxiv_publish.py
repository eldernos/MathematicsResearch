#!/usr/bin/env python3
"""Prepare, and on explicit request publish, one manuscript on alphaXiv's AI Track.

    python3 -B scripts/alphaxiv_publish.py papers/06-multiplicative-lambert                 # dry run
    python3 -B scripts/alphaxiv_publish.py papers/06-multiplicative-lambert \\
        --publish --release manuscripts-v2.0.0                                            # needs ALPHAXIV_API_KEY

Dry run (the default) never contacts alphaXiv. It validates the PDF against papers/SHA256SUMS and prints the
exact `publish_paper` arguments, including unconfirmed disclosure metadata (with a warning), so they can be
inspected before the owner confirms them.

Publishing is refused unless every one of these holds:
  * the owner has set `owner_confirmed = true` in the manuscript's submission/alphaxiv.toml;
  * --release names an approved release (papers/manifest.toml `release`), that tag exists locally, the
    checked-out commit is exactly the tagged commit, and the working tree is clean;
  * the PDF bytes match the checksum recorded in papers/SHA256SUMS *at the tag*;
  * the manuscript is not already recorded at the same version in papers/alphaxiv-records.toml.

alphaXiv documents an MCP server (Streamable HTTP, JSON-RPC) at https://api.alphaxiv.org/mcp/v1 that accepts a
personal API key as a Bearer token. `get_upload_instructions` returns an upload command answering with a
`pdfId`; `publish_paper` then submits. The API key is only ever sent to https hosts under alphaxiv.org. An upload
destination elsewhere (for example a presigned storage URL) receives no credentials, and any other scheme is
refused. Nothing is executed through a shell. Requests carry an explicit User-Agent, because the default Python
agent is rejected by alphaXiv's front end. Licence and subject category are not API parameters; set them in the
alphaXiv web form. Records are keyed by the manuscript's permanent identifier (metadata `id`), so every later
revision of that manuscript is posted with `new_version_of` and keeps one alphaXiv URL.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shlex
import subprocess
import sys
import tomllib
import urllib.parse
import urllib.request
import uuid
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ENDPOINT = "https://api.alphaxiv.org/mcp/v1"
TRUSTED_SUFFIX = "alphaxiv.org"
USER_AGENT = "MathematicsResearch-alphaxiv-publish/1.1 (+https://github.com/eldernos/MathematicsResearch)"
PROTOCOL = "2025-06-18"
STAGES = ("idea", "literature", "experiments", "analysis", "writing")
RATINGS = {"ai", "mixed", "human"}
RECORDS = ROOT / "papers" / "alphaxiv-records.toml"
FORWARDED_HEADERS = {"content-type", "x-upload-token", "x-pdf-upload-token"}


class Refusal(SystemExit):
    pass


def load_toml(path: Path) -> dict:
    return tomllib.loads(path.read_text(encoding="utf-8")) if path.is_file() else {}


def git(*args: str) -> str:
    result = subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True)
    if result.returncode:
        raise Refusal(f"git {' '.join(args)} failed: {result.stderr.strip()}")
    return result.stdout


def trusted_host(url: str) -> bool:
    parts = urllib.parse.urlsplit(url)
    host = (parts.hostname or "").lower()
    return parts.scheme == "https" and (host == TRUSTED_SUFFIX or host.endswith("." + TRUSTED_SUFFIX))


def manuscript(paper_dir: Path) -> tuple[dict, dict]:
    meta = load_toml(paper_dir / "metadata.toml")
    sub = load_toml(paper_dir / "submission" / "alphaxiv.toml")
    if not meta:
        raise Refusal(f"{paper_dir}/metadata.toml is missing")
    if not sub:
        raise Refusal(f"{paper_dir}/submission/alphaxiv.toml is missing")
    return meta, sub


def find_record(meta: dict) -> dict | None:
    for record in load_toml(RECORDS).get("record", []):
        if record.get("id") == meta["id"]:
            return record
    return None


def build_request(paper_dir: Path) -> tuple[dict, bool]:
    """Return the validated publish arguments (without pdf_id) and whether the owner has confirmed them."""
    meta, sub = manuscript(paper_dir)
    disclosure = sub.get("ai_disclosure", {})
    stages = disclosure.get("stages", {})
    if set(stages) != set(STAGES) or not set(stages.values()) <= RATINGS:
        raise Refusal(f"ai_disclosure.stages must rate exactly {STAGES} as ai, mixed or human")
    tools = disclosure.get("tools", [])
    if len(tools) > 10 or (not tools and set(stages.values()) != {"human"}):
        raise Refusal("ai_disclosure.tools must list 1-10 tools unless every stage is human")
    for tool in tools:
        if set(tool) - {"model", "harness", "contribution"} or not tool.get("model") or not tool.get("contribution"):
            raise Refusal(f"invalid tool record: {tool}")
    args = {
        "title": meta["title"],
        "abstract": " ".join(meta["abstract"].split()),
        "authors": list(meta.get("authors", [])),
        "ai_disclosure": {"stages": stages, "tools": [{"model": t["model"], "harness": t.get("harness"),
                                                        "contribution": t["contribution"]} for t in tools]},
    }
    record = find_record(meta)
    if record and record.get("alphaxiv"):
        args["new_version_of"] = record["alphaxiv"]
    elif sub.get("url_slug"):
        args["url_slug"] = sub["url_slug"]
    if len(args["title"]) > 500 or len(args["abstract"]) > 10000 or len(args["authors"]) > 100:
        raise Refusal("title, abstract or author list exceeds alphaXiv's documented limits")
    return args, bool(sub.get("owner_confirmed", False))


def check_pdf(paper_dir: Path, revision: str | None) -> Path:
    """The PDF must match papers/SHA256SUMS in the working tree, or at `revision` when given."""
    pdf = paper_dir / "paper.pdf"
    data = pdf.read_bytes()
    if not data.startswith(b"%PDF-") or len(data) > 50 * 1024 * 1024:
        raise Refusal(f"{pdf} is not a PDF under 50 MB")
    line = f"{hashlib.sha256(data).hexdigest()}  papers/{paper_dir.name}/paper.pdf"
    sums = (git("show", f"{revision}:papers/SHA256SUMS") if revision
            else (ROOT / "papers" / "SHA256SUMS").read_text(encoding="utf-8"))
    if line not in sums.splitlines():
        raise Refusal(f"{pdf} does not match papers/SHA256SUMS{' at ' + revision if revision else ''}")
    return pdf


def check_release(meta: dict, release: str) -> None:
    approved = load_toml(ROOT / "papers" / "manifest.toml").get("release")
    if release != approved or not re.fullmatch(r"manuscripts-v\d+\.\d+\.\d+", release):
        raise Refusal(f"{release!r} is not the approved release ({approved!r})")
    tagged = git("rev-parse", "--verify", "--quiet", f"refs/tags/{release}^{{commit}}").strip()
    head = git("rev-parse", "HEAD").strip()
    if tagged != head:
        raise Refusal(f"the checkout ({head[:12]}) is not the commit tagged {release} ({tagged[:12]})")
    if git("status", "--porcelain", "--untracked-files=no").strip():
        raise Refusal("the working tree has uncommitted changes")
    record = find_record(meta)
    if record and any(v.get("version") == meta["version"] for v in record.get("versions", [])):
        raise Refusal(f"{meta['id']} version {meta['version']} is already recorded on alphaXiv")


def post_json(url: str, payload: dict, key: str) -> dict:
    if not trusted_host(url):
        raise Refusal(f"refusing to send credentials to {url}")
    request = urllib.request.Request(url, data=json.dumps(payload).encode(), method="POST", headers={
        "Authorization": f"Bearer {key}", "Content-Type": "application/json", "User-Agent": USER_AGENT,
        "Accept": "application/json, text/event-stream", "MCP-Protocol-Version": PROTOCOL})
    with urllib.request.urlopen(request, timeout=300) as response:
        text = response.read().decode("utf-8")
    if text.lstrip().startswith("{"):
        return json.loads(text)
    events = [line[5:].strip() for line in text.splitlines() if line.startswith("data:")]
    if not events:
        raise Refusal(f"unexpected response from {url}: {text[:200]}")
    return json.loads(events[-1])


def tool(name: str, arguments: dict, key: str) -> str:
    message = post_json(ENDPOINT, {"jsonrpc": "2.0", "id": str(uuid.uuid4()), "method": "tools/call",
                                   "params": {"name": name, "arguments": arguments}}, key)
    if "error" in message:
        raise Refusal(f"alphaXiv {name} error: {message['error']}")
    result = message["result"]
    if result.get("isError"):
        raise Refusal(f"alphaXiv {name} failed: {result}")
    return "\n".join(part.get("text", "") for part in result.get("content", []))


def upload(pdf: Path, key: str) -> str:
    """Interpret the server's curl instructions without running them, and upload the PDF with urllib."""
    instructions = tool("get_upload_instructions", {}, key)
    match = re.search(r"curl\s.+?(?=\n\s*\n|\Z)", instructions, re.S)
    if not match:
        raise Refusal(f"no upload command in the instructions:\n{instructions}")
    argv = shlex.split(match.group(0).replace("\\\n", " "))
    urls = [a for a in argv if re.match(r"https?://", a)]
    if len(urls) != 1:
        raise Refusal(f"expected one upload URL, found {urls}")
    url = urls[0]
    if urllib.parse.urlsplit(url).scheme != "https":
        raise Refusal(f"refusing a non-https upload URL: {url}")
    headers = {"User-Agent": USER_AGENT}
    field = "file"
    for i, arg in enumerate(argv[:-1]):
        if arg in ("-H", "--header"):
            name, _, value = argv[i + 1].partition(":")
            if name.strip().lower() in FORWARDED_HEADERS:
                headers[name.strip()] = value.strip()
        elif arg in ("-F", "--form"):
            field = argv[i + 1].split("=", 1)[0]
    if trusted_host(url):
        headers["Authorization"] = f"Bearer {key}"   # the key goes only to alphaxiv.org hosts
    boundary = uuid.uuid4().hex
    body = (f"--{boundary}\r\nContent-Disposition: form-data; name=\"{field}\"; filename=\"{pdf.name}\"\r\n"
            "Content-Type: application/pdf\r\n\r\n").encode() + pdf.read_bytes() + f"\r\n--{boundary}--\r\n".encode()
    headers["Content-Type"] = f"multipart/form-data; boundary={boundary}"
    with urllib.request.urlopen(urllib.request.Request(url, data=body, method="POST", headers=headers),
                                timeout=300) as response:
        reply = json.loads(response.read().decode("utf-8"))
    pdf_id = reply.get("pdfId")
    if not isinstance(pdf_id, str) or not re.fullmatch(r"[0-9a-fA-F-]{8,64}", pdf_id):
        raise Refusal(f"unexpected upload reply: {reply}")
    return pdf_id


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("paper", type=Path, help="manuscript directory, for example papers/06-multiplicative-lambert")
    parser.add_argument("--publish", action="store_true", help="upload and submit (default: dry run)")
    parser.add_argument("--release", help="approved release tag; required with --publish")
    parser.add_argument("--result", type=Path, help="write the alphaXiv response as JSON here")
    args = parser.parse_args()
    paper_dir = (args.paper if args.paper.is_absolute() else ROOT / args.paper).resolve()
    if paper_dir.parent != (ROOT / "papers").resolve() or not re.fullmatch(r"\d\d-[a-z0-9.-]+", paper_dir.name):
        raise Refusal(f"{args.paper} is not a manuscript directory under papers/")
    meta, _ = manuscript(paper_dir)
    request, confirmed = build_request(paper_dir)
    if args.publish:
        if not confirmed:
            raise Refusal("the owner has not confirmed this disclosure (set owner_confirmed = true after review)")
        if not args.release:
            raise Refusal("--publish requires --release <approved tag>")
        check_release(meta, args.release)
        pdf = check_pdf(paper_dir, args.release)
    else:
        pdf = check_pdf(paper_dir, None)
    print(json.dumps({"manuscript": meta["id"], "version": meta["version"], "pdf": pdf.relative_to(ROOT).as_posix(),
                      "owner_confirmed": confirmed, "publish_paper": request}, indent=2, ensure_ascii=False))
    if not args.publish:
        if not confirmed:
            print("Warning: the owner has not confirmed this disclosure; publishing would be refused.", file=sys.stderr)
        print("Dry run: nothing was sent to alphaXiv.", file=sys.stderr)
        return
    key = os.environ.get("ALPHAXIV_API_KEY", "")
    if not key:
        raise Refusal("ALPHAXIV_API_KEY is not set")
    request["pdf_id"] = upload(pdf, key)
    response = tool("publish_paper", request, key)
    print(response)
    try:
        outcome = json.loads(response)
    except json.JSONDecodeError:
        outcome = {"raw": response}
    record = {"id": meta["id"], "dir": paper_dir.name, "version": meta["version"], "release": args.release,
              "status": outcome.get("status"), "url": outcome.get("url"), "response": outcome}
    if args.result:
        args.result.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    if outcome.get("status") not in ("published", "in_review"):
        raise Refusal(f"alphaXiv did not accept the submission: {outcome}")


if __name__ == "__main__":
    main()
