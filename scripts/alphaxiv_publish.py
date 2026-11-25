#!/usr/bin/env python3
"""Prepare, and on explicit request publish, one manuscript on alphaXiv's AI Track.

    python3 -B scripts/alphaxiv_publish.py papers/06-multiplicative-lambert            # dry run (default)
    python3 -B scripts/alphaxiv_publish.py papers/06-multiplicative-lambert --publish  # needs ALPHAXIV_API_KEY

The dry run validates the PDF and its checksum and prints the exact `publish_paper` arguments, without
contacting alphaXiv. Publishing uses alphaXiv's documented MCP server (Streamable HTTP, JSON-RPC,
https://api.alphaxiv.org/mcp/v1) with a personal API key sent as a Bearer token: `get_upload_instructions`
returns an upload command, which answers with a `pdfId`, and `publish_paper` then submits the paper. The
upload request is taken from the server's instructions at run time because alphaXiv does not document it
statically. Licence and subject category are not API fields; set them in the alphaXiv web form.

Inputs per manuscript: metadata.toml, paper.pdf and submission/alphaxiv.toml (AI disclosure, slug).
Earlier alphaXiv records live in papers/alphaxiv-records.toml; a recorded paper is published as a new version.
Nothing is sent unless --publish is given, and every submission is screened by alphaXiv (screening is not
peer review). Only one submission per account can be in progress at a time.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shlex
import sys
import tomllib
import urllib.request
import uuid
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ENDPOINT = "https://api.alphaxiv.org/mcp/v1"
STAGES = ("idea", "literature", "experiments", "analysis", "writing")
RATINGS = {"ai", "mixed", "human"}


def load_toml(path: Path) -> dict:
    return tomllib.loads(path.read_text(encoding="utf-8")) if path.is_file() else {}


def build_request(paper_dir: Path) -> dict:
    """Return the validated publish arguments, without the pdf_id that the upload provides."""
    meta = load_toml(paper_dir / "metadata.toml")
    sub = load_toml(paper_dir / "submission" / "alphaxiv.toml")
    if not meta:
        raise SystemExit(f"{paper_dir}/metadata.toml is missing")
    if not sub:
        raise SystemExit(f"{paper_dir}/submission/alphaxiv.toml is missing")
    if not sub.get("owner_confirmed", False):
        raise SystemExit(f"{paper_dir}/submission/alphaxiv.toml: the owner has not confirmed this disclosure "
                         "(set owner_confirmed = true after reviewing it)")
    disclosure = sub.get("ai_disclosure", {})
    stages = disclosure.get("stages", {})
    if set(stages) != set(STAGES) or not set(stages.values()) <= RATINGS:
        raise SystemExit(f"ai_disclosure.stages must rate exactly {STAGES} as ai, mixed or human")
    tools = disclosure.get("tools", [])
    if len(tools) > 10 or (not tools and set(stages.values()) != {"human"}):
        raise SystemExit("ai_disclosure.tools must list 1-10 tools unless every stage is human")
    for tool in tools:
        if set(tool) - {"model", "harness", "contribution"} or not tool.get("model") or not tool.get("contribution"):
            raise SystemExit(f"invalid tool record: {tool}")
    args = {
        "title": meta["title"],
        "abstract": " ".join(meta["abstract"].split()),
        "authors": list(meta.get("authors", [])),
        "ai_disclosure": {"stages": stages, "tools": [{"model": t["model"], "harness": t.get("harness"),
                                                        "contribution": t["contribution"]} for t in tools]},
    }
    records = load_toml(ROOT / "papers" / "alphaxiv-records.toml").get("record", [])
    previous = next((r for r in records if r.get("dir") == paper_dir.name), None)
    if previous and previous.get("alphaxiv"):
        args["new_version_of"] = previous["alphaxiv"]
    elif sub.get("url_slug"):
        args["url_slug"] = sub["url_slug"]
    if len(args["title"]) > 500 or len(args["abstract"]) > 10000 or len(args["authors"]) > 100:
        raise SystemExit("title, abstract or author list exceeds alphaXiv's documented limits")
    return args


def check_pdf(paper_dir: Path) -> Path:
    pdf = paper_dir / "paper.pdf"
    data = pdf.read_bytes()
    if not data.startswith(b"%PDF-") or len(data) > 50 * 1024 * 1024:
        raise SystemExit(f"{pdf} is not a PDF under 50 MB")
    expected = f"{hashlib.sha256(data).hexdigest()}  papers/{paper_dir.name}/paper.pdf"
    sums = (ROOT / "papers" / "SHA256SUMS").read_text(encoding="utf-8").splitlines()
    if expected not in sums:
        raise SystemExit(f"{pdf} does not match papers/SHA256SUMS; publish only a recorded release PDF")
    return pdf


def rpc(method: str, params: dict, key: str) -> dict:
    body = json.dumps({"jsonrpc": "2.0", "id": str(uuid.uuid4()), "method": method, "params": params}).encode()
    request = urllib.request.Request(ENDPOINT, data=body, method="POST", headers={
        "Authorization": f"Bearer {key}", "Content-Type": "application/json",
        "Accept": "application/json, text/event-stream"})
    with urllib.request.urlopen(request, timeout=300) as response:
        text = response.read().decode("utf-8")
    if text.lstrip().startswith("{"):
        message = json.loads(text)
    else:  # Server-sent events: take the last JSON-RPC message.
        events = [line[5:].strip() for line in text.splitlines() if line.startswith("data:")]
        message = json.loads(events[-1])
    if "error" in message:
        raise SystemExit(f"alphaXiv {method} error: {message['error']}")
    return message["result"]


def tool(name: str, arguments: dict, key: str) -> str:
    result = rpc("tools/call", {"name": name, "arguments": arguments}, key)
    if result.get("isError"):
        raise SystemExit(f"alphaXiv {name} failed: {result}")
    return "\n".join(part.get("text", "") for part in result.get("content", []))


def upload(pdf: Path, key: str) -> str:
    """Follow the server's curl instructions with urllib, sending the PDF as multipart form data."""
    instructions = tool("get_upload_instructions", {}, key)
    match = re.search(r"curl\s.+?(?=\n\n|\Z)", instructions, re.S)
    if not match:
        raise SystemExit(f"could not find an upload command in the instructions:\n{instructions}")
    argv = shlex.split(match.group(0).replace("\\\n", " "))
    url = next(a for a in argv if a.startswith("https://"))
    headers = {argv[i + 1].split(":", 1)[0].strip(): argv[i + 1].split(":", 1)[1].strip()
               for i, a in enumerate(argv[:-1]) if a in ("-H", "--header")}
    field = next((argv[i + 1].split("=", 1)[0] for i, a in enumerate(argv[:-1]) if a in ("-F", "--form")), "file")
    boundary = uuid.uuid4().hex
    body = (f"--{boundary}\r\nContent-Disposition: form-data; name=\"{field}\"; filename=\"{pdf.name}\"\r\n"
            f"Content-Type: application/pdf\r\n\r\n").encode() + pdf.read_bytes() + f"\r\n--{boundary}--\r\n".encode()
    headers["Content-Type"] = f"multipart/form-data; boundary={boundary}"
    headers.setdefault("Authorization", f"Bearer {key}")
    with urllib.request.urlopen(urllib.request.Request(url, data=body, method="POST", headers=headers),
                                timeout=300) as response:
        reply = json.loads(response.read().decode("utf-8"))
    return reply["pdfId"]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("paper", type=Path, help="manuscript directory, for example papers/06-multiplicative-lambert")
    parser.add_argument("--publish", action="store_true", help="actually upload and submit (default: dry run)")
    parser.add_argument("--result", type=Path, help="write the alphaXiv response as JSON here")
    args = parser.parse_args()
    paper_dir = (ROOT / args.paper).resolve() if not args.paper.is_absolute() else args.paper
    pdf = check_pdf(paper_dir)
    request = build_request(paper_dir)
    print(json.dumps({"pdf": str(pdf.relative_to(ROOT)), "publish_paper": request}, indent=2, ensure_ascii=False))
    if not args.publish:
        print("Dry run: nothing was sent to alphaXiv.", file=sys.stderr)
        return
    key = os.environ.get("ALPHAXIV_API_KEY")
    if not key:
        raise SystemExit("ALPHAXIV_API_KEY is not set")
    request["pdf_id"] = upload(pdf, key)
    response = tool("publish_paper", request, key)
    print(response)
    if args.result:
        args.result.write_text(json.dumps({"dir": paper_dir.name, "response": response}, indent=2) + "\n",
                               encoding="utf-8")


if __name__ == "__main__":
    main()
