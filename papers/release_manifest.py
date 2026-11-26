#!/usr/bin/env python3
"""Write the release manifest for the manuscript release named in papers/manifest.toml.

    python3 -B papers/release_manifest.py --json release-manifest.json   # release asset
    python3 -B papers/release_manifest.py --markdown papers/RELEASES.md   # committed record

The JSON identifies every paper version, its source directory, the source commit, the pinned
Lean commit and the SHA-256 of each PDF, together with the immutable earlier releases.
"""
import argparse
import hashlib
import json
import subprocess
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = tomllib.loads((ROOT / "papers" / "manifest.toml").read_text(encoding="utf-8"))
REPO = "https://github.com/eldernos/MathematicsResearch"


def git(*args):
    return subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True,
                          check=True).stdout.strip()


def archived_titles():
    data = tomllib.loads((ROOT / "docs" / "registry" / "papers.toml").read_text(encoding="utf-8"))
    return {Path(p["dir"]).name: p["title"] for p in data["paper"]}


def entries():
    titles = archived_titles()
    rows = []
    for entry in MANIFEST["paper"]:
        folder = ROOT / "papers" / entry["dir"]
        pdf = folder / "paper.pdf"
        if not pdf.is_file():
            continue
        meta_path = folder / "metadata.toml"
        meta = tomllib.loads(meta_path.read_text(encoding="utf-8")) if meta_path.is_file() else {}
        rows.append({
            "paper": entry["id"],
            "title": meta.get("title", titles.get(entry["dir"], entry["dir"])),
            "version": entry["version"],
            "status": "archived (unchanged since manuscripts-v1.1.0)" if entry.get("archived")
                      else meta.get("status", "preprint draft"),
            "batch": entry.get("batch"),
            "supersedes": entry.get("supersedes", ""),
            "superseded_by": entry.get("superseded_by", ""),
            "path": f"papers/{entry['dir']}/paper.pdf",
            "asset": f"{entry['dir']}.pdf",
            "sha256": hashlib.sha256(pdf.read_bytes()).hexdigest(),
        })
    return rows


def build(commit):
    history = [{"tag": h["tag"], "commit": h["commit"],
                "pdf_sha256": h["sha256"]} for h in MANIFEST["history"]]
    return {
        "release": MANIFEST["release"],
        "commit": commit,
        "lean_commit": MANIFEST["lean_commit"],
        "baseline": {"tag": "research-checkpoint-18", "commit": MANIFEST["lean_commit"]},
        "previous_release": {"tag": MANIFEST["history"][-1]["tag"],
                             "commit": MANIFEST["history"][-1]["commit"]},
        "review_status": "AI cross-provider review only; no independent human peer review",
        "manuscripts": entries(),
        "history": history,
    }


def markdown(data):
    lines = [
        "# Manuscript releases",
        "",
        "Every manuscript release is a Git tag. A tag is never moved and earlier files are never replaced:",
        "a revision appears in a new directory with a new version number. The table lists the release",
        f"candidate {data['release']}. Its Lean links point to the immutable commit",
        f"[`{data['lean_commit'][:12]}`]({REPO}/tree/{data['lean_commit']}) (research-checkpoint-18).",
        "The SHA-256 digests identify the PDFs committed at the source commit of this record.",
        "",
        "| Paper | Version | Title | Status | PDF | SHA-256 |",
        "| --- | --- | --- | --- | --- | --- |",
    ]
    for row in data["manuscripts"]:
        lines.append(f"| {row['paper']} | {row['version']} | {row['title']} | {row['status']} | "
                     f"[{row['asset']}]({Path(row['path']).relative_to('papers').as_posix()}) | `{row['sha256']}` |")
    lines += ["", "## Earlier releases", "",
              "These tags remain valid. `python3 -B papers/check_release.py --verify-history` checks that",
              "each still names its commit and the recorded bytes of every PDF.", ""]
    for release in data["history"]:
        lines += [f"### {release['tag']}", "",
                  f"Commit [`{release['commit']}`]({REPO}/tree/{release['commit']}) · "
                  f"[GitHub release]({REPO}/releases/tag/{release['tag']})", "",
                  "| PDF | SHA-256 |", "| --- | --- |"]
        lines += [f"| papers/{name}/paper.pdf | `{sha}` |" for name, sha in release["pdf_sha256"].items()]
        lines.append("")
    lines += ["## Review status", "",
              "All manuscripts are preprint drafts. Their written proofs and literature comparisons have been",
              "reviewed only by AI models from several providers. Cross-model review is not independent human",
              "peer review, and no manuscript has been submitted to or accepted by a journal.", ""]
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--commit", help="source commit (default: HEAD)")
    parser.add_argument("--json", type=Path, help="write the JSON release manifest here")
    parser.add_argument("--markdown", type=Path, help="write the Markdown release record here")
    args = parser.parse_args()
    data = build(args.commit or git("rev-parse", "HEAD"))
    if args.json:
        args.json.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8", newline="\n")
    if args.markdown:
        args.markdown.write_text(markdown(data), encoding="utf-8", newline="\n")
    if not (args.json or args.markdown):
        print(json.dumps(data, indent=2))


if __name__ == "__main__":
    main()
