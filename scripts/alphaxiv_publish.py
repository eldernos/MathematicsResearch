#!/usr/bin/env python3
"""Prepare, and on explicit request publish, one manuscript on alphaXiv's AI Track.

    python3 -B scripts/alphaxiv_publish.py papers/06-multiplicative-lambert                 # dry run
    python3 -B scripts/alphaxiv_publish.py papers/06-multiplicative-lambert \\
        --publish --release manuscripts-v2.0.0                                            # needs ALPHAXIV_API_KEY

Two kinds of input are kept apart:

* **Release content** (the PDF, its checksum and the manuscript metadata: title, abstract, authors) comes from
  the checked-out tree. For publication that tree must be exactly the approved release tag.
* **Submission state** (the owner's confirmation and AI disclosure in submission/alphaxiv.toml, and the alphaXiv
  records in papers/alphaxiv-records.toml) is mutable after a release. For publication it is read from the
  control ref, by default `refs/remotes/origin/main`. A confirmation or record committed to main after the tag
  therefore takes effect, and a recorded version is never resubmitted.

Dry run (the default) never contacts alphaXiv. It prints the exact `publish_paper` arguments, including disclosure
metadata that is not yet confirmed (with a warning). It works on any branch, and no tag is needed.

Publishing is refused unless the owner has confirmed the disclosure (on the control ref), --release names the
approved release (papers/manifest.toml), HEAD is exactly that tag with a clean tree, the PDF matches
papers/SHA256SUMS at the tag, and that manuscript version is not already recorded.

alphaXiv documents an MCP server at https://api.alphaxiv.org/mcp/v1 (Streamable HTTP, JSON-RPC, stateless). It
accepts a personal API key as a Bearer token. `get_upload_instructions` returns an upload command answering with
a `pdfId`; `publish_paper` then submits. Credentials are sent only to https hosts under alphaxiv.org on the
default port. Redirects are refused, server-supplied commands are parsed and never executed, and requests carry an
explicit User-Agent, which alphaXiv's front end requires. Licence and subject category are not API parameters;
set them in the alphaXiv web form. Records are keyed by the permanent manuscript number (metadata `id`), so a
revision is posted with `new_version_of` and keeps one alphaXiv URL.
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
import urllib.error
import urllib.parse
import urllib.request
import uuid
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ENDPOINT = "https://api.alphaxiv.org/mcp/v1"
TRUSTED_SUFFIX = "alphaxiv.org"
USER_AGENT = "MathematicsResearch-alphaxiv-publish/1.2 (+https://github.com/eldernos/MathematicsResearch)"
PROTOCOL = "2025-06-18"
STAGES = ("idea", "literature", "experiments", "analysis", "writing")
RATINGS = {"ai", "mixed", "human"}
RECORDS_PATH = "papers/alphaxiv-records.toml"
DEFAULT_CONTROL_REF = "refs/remotes/origin/main"
# Headers from the server's upload instructions that may be forwarded. Authorization is never taken from them.
FORWARDED_HEADER = re.compile(r"(content-type|x-[a-z0-9-]+)", re.I)
LABEL = re.compile(r"[a-z0-9](?:[a-z0-9-]{0,61}[a-z0-9])?")


class Refusal(SystemExit):
    pass


class _NoRedirect(urllib.request.HTTPRedirectHandler):
    """Refuse every redirect, so a request carrying the API key can never be forwarded to another host."""

    def redirect_request(self, req, fp, code, msg, headers, newurl):
        raise Refusal(f"refusing redirect {code} from {req.full_url} to {newurl}")


OPENER = urllib.request.build_opener(_NoRedirect)


def git(*args: str, check: bool = True) -> str:
    result = subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True)
    if result.returncode and check:
        raise Refusal(f"git {' '.join(args)} failed: {result.stderr.strip()}")
    return result.stdout if not result.returncode else ""


def read_text(path: str, ref: str | None) -> str:
    """File text from the working tree, or from `ref` when given ('' if absent)."""
    if ref:
        return git("show", f"{ref}:{path}", check=False)
    file = ROOT / path
    return file.read_text(encoding="utf-8") if file.is_file() else ""


def read_toml(path: str, ref: str | None = None) -> dict:
    text = read_text(path, ref)
    return tomllib.loads(text) if text else {}


def trusted_host(url: str) -> bool:
    parts = urllib.parse.urlsplit(url)
    if parts.scheme != "https" or parts.username or parts.password:
        return False
    try:
        if parts.port not in (None, 443):
            return False
    except ValueError:
        return False
    host = (parts.hostname or "").lower()
    if host.endswith("."):
        host = host[:-1]
    labels = host.split(".")
    if not all(LABEL.fullmatch(label) for label in labels):
        return False  # rejects empty labels, underscores and non-ASCII (IDN) hosts
    return host == TRUSTED_SUFFIX or host.endswith("." + TRUSTED_SUFFIX)


def find_record(manuscript_id: str, control_ref: str | None) -> dict | None:
    for record in read_toml(RECORDS_PATH, control_ref).get("record", []):
        if record.get("id") == manuscript_id:
            return record
    return None


def load_inputs(paper_dir: Path, control_ref: str | None) -> tuple[dict, dict]:
    rel = paper_dir.relative_to(ROOT).as_posix()
    meta = read_toml(f"{rel}/metadata.toml")
    if not meta:
        raise Refusal(f"{rel}/metadata.toml is missing")
    sub = read_toml(f"{rel}/submission/alphaxiv.toml", control_ref)
    if not sub:
        raise Refusal(f"{rel}/submission/alphaxiv.toml is missing{' at ' + control_ref if control_ref else ''}")
    meta["id"] = str(meta.get("id", "")).strip()
    if not re.fullmatch(r"[IVX]+", meta["id"]):
        raise Refusal(f"{rel}/metadata.toml: id {meta['id']!r} is not a permanent manuscript number")
    return meta, sub


def build_request(meta: dict, sub: dict, control_ref: str | None) -> tuple[dict, bool]:
    """Return the validated publish arguments (without pdf_id) and whether the owner has confirmed them."""
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
    record = find_record(meta["id"], control_ref)
    if record:
        target = str(record.get("alphaxiv", ""))
        if not trusted_host(target):
            raise Refusal(f"record for {meta['id']} has no valid https alphaxiv.org URL: {target!r}")
        args["new_version_of"] = target
    elif sub.get("url_slug"):
        slug = str(sub["url_slug"])
        if len(slug) > 120 or not re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", slug):
            raise Refusal(f"invalid url_slug {slug!r} (lowercase words joined by hyphens, at most 120 characters)")
        args["url_slug"] = slug
    if len(args["title"]) > 500 or len(args["abstract"]) > 10000 or len(args["authors"]) > 100:
        raise Refusal("title, abstract or author list exceeds alphaXiv's documented limits")
    return args, sub.get("owner_confirmed") is True


def check_pdf(paper_dir: Path, revision: str | None) -> Path:
    """The PDF must match papers/SHA256SUMS in the working tree, or at `revision` when given."""
    pdf = paper_dir / "paper.pdf"
    data = pdf.read_bytes()
    if not data.startswith(b"%PDF-") or len(data) > 50 * 1024 * 1024:
        raise Refusal(f"{pdf} is not a PDF under 50 MB")
    line = f"{hashlib.sha256(data).hexdigest()}  papers/{paper_dir.name}/paper.pdf"
    if line not in read_text("papers/SHA256SUMS", revision).splitlines():
        raise Refusal(f"{pdf} does not match papers/SHA256SUMS{' at ' + revision if revision else ''}")
    return pdf


def check_release(meta: dict, release: str, control_ref: str) -> None:
    approved = read_toml("papers/manifest.toml").get("release")
    if release != approved or not re.fullmatch(r"manuscripts-v\d+\.\d+\.\d+", release):
        raise Refusal(f"{release!r} is not the approved release ({approved!r})")
    tagged = git("rev-parse", "--verify", "--quiet", f"refs/tags/{release}^{{commit}}", check=False).strip()
    if not tagged:
        raise Refusal(f"the release tag {release} does not exist in this clone")
    head = git("rev-parse", "HEAD").strip()
    if tagged != head:
        raise Refusal(f"the checkout ({head[:12]}) is not the commit tagged {release} ({tagged[:12]})")
    if git("status", "--porcelain", "--untracked-files=no").strip():
        raise Refusal("the working tree has uncommitted changes")
    if not git("rev-parse", "--verify", "--quiet", control_ref, check=False).strip():
        raise Refusal(f"the control ref {control_ref} is not available; fetch the default branch first")
    record = find_record(meta["id"], control_ref)
    if record and any(str(v.get("version")) == str(meta["version"]) for v in record.get("versions", [])):
        raise Refusal(f"manuscript {meta['id']} version {meta['version']} is already recorded on alphaXiv")


def post_json(url: str, payload: dict, key: str) -> dict:
    if not trusted_host(url):
        raise Refusal(f"refusing to send credentials to {url}")
    request = urllib.request.Request(url, data=json.dumps(payload).encode(), method="POST", headers={
        "Authorization": f"Bearer {key}", "Content-Type": "application/json", "User-Agent": USER_AGENT,
        "Accept": "application/json, text/event-stream", "MCP-Protocol-Version": PROTOCOL})
    try:
        with OPENER.open(request, timeout=300) as response:
            text = response.read().decode("utf-8")
    except urllib.error.HTTPError as err:
        raise Refusal(f"HTTP {err.code} from {url}: {err.read()[:300]!r}") from None
    if text.lstrip().startswith("{"):
        return json.loads(text)
    messages = []
    for block in re.split(r"\r?\n\r?\n", text):  # one server-sent event per block
        data = "\n".join(line[5:].lstrip() for line in block.splitlines() if line.startswith("data:"))
        if data:
            try:
                messages.append(json.loads(data))
            except json.JSONDecodeError:
                continue
    for message in reversed(messages):
        if message.get("id") == payload.get("id") and ("result" in message or "error" in message):
            return message
    raise Refusal(f"no JSON-RPC response for request {payload.get('id')} from {url}")


def tool(name: str, arguments: dict, key: str) -> str:
    request_id = str(uuid.uuid4())
    message = post_json(ENDPOINT, {"jsonrpc": "2.0", "id": request_id, "method": "tools/call",
                                   "params": {"name": name, "arguments": arguments}}, key)
    if "error" in message:
        raise Refusal(f"alphaXiv {name} error: {message['error']}")
    result = message["result"]
    if result.get("isError"):
        raise Refusal(f"alphaXiv {name} failed: {result}")
    return "\n".join(part.get("text", "") for part in result.get("content", []))


def parse_upload_command(instructions: str) -> tuple[str, dict, dict, str]:
    """From the server's text, return (url, headers, plain form fields, file field). Nothing is executed."""
    text = re.sub(r"```[a-zA-Z]*", "\n", instructions)
    lines = text.splitlines()
    start = next((i for i, l in enumerate(lines) if re.match(r"\s*curl\s", l)), None)
    if start is None:
        raise Refusal(f"no upload command in the instructions:\n{instructions}")
    command = []
    for line in lines[start:]:
        command.append(line.rstrip().removesuffix("\\"))
        if not line.rstrip().endswith("\\"):
            break
    try:
        argv = shlex.split(" ".join(command))
    except ValueError as err:
        raise Refusal(f"cannot parse the upload command ({err}): {' '.join(command)[:300]}") from None
    urls = [a for a in argv if re.match(r"https?://", a, re.I)]
    if len(urls) != 1:
        raise Refusal(f"expected one upload URL, found {urls}")
    url = urls[0]
    if urllib.parse.urlsplit(url).scheme.lower() != "https":
        raise Refusal(f"refusing a non-https upload URL: {url}")
    headers: dict[str, str] = {}
    fields: dict[str, str] = {}
    file_field = ""
    for i, arg in enumerate(argv[:-1]):
        value = argv[i + 1]
        if arg in ("-H", "--header"):
            name, _, header_value = value.partition(":")
            name = name.strip()
            if FORWARDED_HEADER.fullmatch(name) and "\r" not in header_value and "\n" not in header_value:
                headers[name.lower()] = header_value.strip()
        elif arg in ("-F", "--form"):
            name, _, field_value = value.partition("=")
            if not re.fullmatch(r"[A-Za-z0-9_.\-\[\]]+", name):
                raise Refusal(f"unsafe form field name {name!r}")
            if field_value.startswith("@"):
                file_field = name
            else:
                fields[name] = field_value
    return url, headers, fields, file_field or "file"


def upload(pdf: Path, key: str) -> str:
    url, extra, fields, file_field = parse_upload_command(tool("get_upload_instructions", {}, key))
    headers = {"user-agent": USER_AGENT, **{k: v for k, v in extra.items() if k != "content-type"}}
    if trusted_host(url):
        headers["authorization"] = f"Bearer {key}"  # the key goes only to alphaxiv.org hosts
    boundary = uuid.uuid4().hex
    body = b"".join(f"--{boundary}\r\nContent-Disposition: form-data; name=\"{k}\"\r\n\r\n{v}\r\n".encode()
                    for k, v in fields.items())
    body += (f"--{boundary}\r\nContent-Disposition: form-data; name=\"{file_field}\"; filename=\"{pdf.name}\"\r\n"
             "Content-Type: application/pdf\r\n\r\n").encode() + pdf.read_bytes() + f"\r\n--{boundary}--\r\n".encode()
    headers["content-type"] = f"multipart/form-data; boundary={boundary}"
    try:
        with OPENER.open(urllib.request.Request(url, data=body, method="POST", headers=headers), timeout=300) as r:
            reply = json.loads(r.read().decode("utf-8"))
    except urllib.error.HTTPError as err:
        raise Refusal(f"upload failed with HTTP {err.code}: {err.read()[:300]!r}") from None
    pdf_id = reply.get("pdfId") if isinstance(reply, dict) else None
    if not isinstance(pdf_id, str) or not re.fullmatch(r"[0-9a-fA-F-]{8,64}", pdf_id):
        raise Refusal(f"unexpected upload reply: {reply}")
    return pdf_id


def parse_outcome(response: str) -> dict:
    try:
        value = json.loads(response)
        return value if isinstance(value, dict) else {"raw": response}
    except json.JSONDecodeError:
        match = re.search(r"\{.*\}", response, re.S)
        if match:
            try:
                return json.loads(match.group(0))
            except json.JSONDecodeError:
                pass
    return {"raw": response}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("paper", type=Path, help="manuscript directory, for example papers/06-multiplicative-lambert")
    parser.add_argument("--publish", action="store_true", help="upload and submit (default: dry run)")
    parser.add_argument("--release", help="approved release tag; required with --publish")
    parser.add_argument("--control-ref", help=f"ref holding the submission state (publish default {DEFAULT_CONTROL_REF})")
    parser.add_argument("--result", type=Path, help="write the alphaXiv response as JSON here")
    args = parser.parse_args()
    paper_dir = (args.paper if args.paper.is_absolute() else ROOT / args.paper).resolve()
    if paper_dir.parent != (ROOT / "papers").resolve() or not re.fullmatch(r"\d\d-[a-z0-9.-]+", paper_dir.name):
        raise Refusal(f"{args.paper} is not a manuscript directory under papers/")
    control_ref = args.control_ref or (DEFAULT_CONTROL_REF if args.publish else None)
    meta, sub = load_inputs(paper_dir, control_ref)
    request, confirmed = build_request(meta, sub, control_ref)
    if args.publish:
        if not confirmed:
            raise Refusal(f"the owner has not confirmed this disclosure on {control_ref} "
                          "(set owner_confirmed = true after review and commit it to the default branch)")
        if not args.release:
            raise Refusal("--publish requires --release <approved tag>")
        check_release(meta, args.release, control_ref)
        pdf = check_pdf(paper_dir, f"refs/tags/{args.release}")
    else:
        pdf = check_pdf(paper_dir, None)
    print(json.dumps({"manuscript": meta["id"], "version": meta["version"], "pdf": pdf.relative_to(ROOT).as_posix(),
                      "submission_state": control_ref or "working tree", "owner_confirmed": confirmed,
                      "publish_paper": request}, indent=2, ensure_ascii=False))
    if not args.publish:
        if not confirmed:
            print("Warning: the owner has not confirmed this disclosure; publishing would be refused.", file=sys.stderr)
        print("Dry run: nothing was sent to alphaXiv.", file=sys.stderr)
        return
    key = os.environ.get("ALPHAXIV_API_KEY", "")
    if not key:
        raise Refusal("ALPHAXIV_API_KEY is not set")
    request["pdf_id"] = upload(pdf, key)
    outcome = parse_outcome(tool("publish_paper", request, key))
    record = {"id": meta["id"], "dir": paper_dir.name, "version": meta["version"], "release": args.release,
              "status": outcome.get("status"), "url": outcome.get("url"), "response": outcome}
    print(json.dumps(record, indent=2))
    if args.result:
        args.result.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    if outcome.get("status") not in ("published", "in_review"):
        raise Refusal(f"alphaXiv did not accept the submission: {outcome}")


if __name__ == "__main__":
    main()
