#!/usr/bin/env python3
"""Check the manuscript PDFs, their source and review companions, and the immutable earlier releases.

The list of manuscripts is papers/manifest.toml. Archived v1.1 directories must match the
checksums recorded for manuscripts-v1.1.0 byte for byte. Each manuscripts-v2 directory must
carry its LaTeX source, bibliography, PDF, metadata, verification map, novelty ledger and
submission drafts.
"""
import argparse
from functools import lru_cache
import hashlib
import re
from pathlib import Path
import shutil
import subprocess
import tomllib
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = tomllib.loads((ROOT / "papers" / "manifest.toml").read_text(encoding="utf-8"))
PAPERS = tuple(entry["dir"] for entry in MANIFEST["paper"])
ARCHIVED_FILES = ("paper.tex", "references.bib", "REVIEW.md", "paper.pdf")
V2_FILES = ("paper.tex", "references.bib", "paper.pdf", "metadata.toml", "VERIFICATION.md", "LEDGER.md")
SUBMISSION_FILES = ("abstract.txt", "alphaxiv.md", "announcement.md", "summary.md",
                    "reviewer-inquiry.md", "reviewer-packet.md")
METADATA_KEYS = ("id", "title", "authors", "affiliation", "short_title", "version", "status", "abstract", "keywords",
                 "msc_primary", "msc_secondary", "supersedes", "lean_commit", "registry_ids")


def digest_bytes(data):
    return hashlib.sha256(data).hexdigest()


def digest(path):
    return digest_bytes(path.read_bytes())


def git(*args, binary=False):
    result = subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=not binary)
    if result.returncode:
        raise ValueError(f"git {' '.join(args)} failed")
    return result.stdout


@lru_cache(maxsize=None)
def source_lines(revision, name):
    try:
        return git("show", f"{revision}:{name}").splitlines()
    except ValueError:
        raise ValueError(f"Missing source object {revision}:{name}") from None


def check_pdf_pins(pdf):
    """Validate the exact Git objects and line anchors embedded in the PDF annotations."""
    result = subprocess.run(["pdfinfo", "-url", str(pdf)], capture_output=True, text=True)
    if result.returncode:
        return [f"Cannot read PDF annotations from {pdf.parent.name}/{pdf.name}"]
    errors = []
    for url in set(re.findall(r"https://github\.com/[^\s]+", result.stdout)):
        link = urlsplit(url)
        parts = unquote(link.path).lstrip("/").split("/", 4)
        if (len(parts) != 5 or parts[:3] != ["eldernos", "MathematicsResearch", "blob"]
                or not parts[4].endswith(".lean")):
            continue
        revision, name = parts[3:]
        if not re.fullmatch(r"[0-9a-f]{7,40}", revision):
            errors.append(f"Unpinned Lean link in {pdf.parent.name}: {url}")
            continue
        try:
            lines = source_lines(revision, name)
        except ValueError as error:
            errors.append(str(error))
            continue
        if link.fragment:
            anchor = re.fullmatch(r"L([1-9][0-9]*)(?:-L([1-9][0-9]*))?", link.fragment)
            if not anchor or any(int(n) > len(lines) for n in anchor.groups() if n):
                errors.append(f"Invalid source line in {pdf.parent.name}: {url}")
    return errors


def check_metadata(entry, folder):
    problems = []
    path = folder / "metadata.toml"
    if not path.is_file():
        return problems
    try:
        data = tomllib.loads(path.read_text(encoding="utf-8"))
    except tomllib.TOMLDecodeError as error:
        return [f"Invalid TOML in {path.relative_to(ROOT)}: {error}"]
    for key in METADATA_KEYS:
        if key not in data:
            problems.append(f"{path.relative_to(ROOT)} lacks `{key}`")
    if str(data.get("version", "")) != entry["version"]:
        problems.append(f"{path.relative_to(ROOT)} version {data.get('version')!r} differs from the manifest")
    if str(data.get("id", "")).split("#")[0].strip() != entry["id"]:
        problems.append(f"{path.relative_to(ROOT)} id {data.get('id')!r} differs from the manifest ({entry['id']!r})")
    if data.get("lean_commit") != MANIFEST["lean_commit"]:
        problems.append(f"{path.relative_to(ROOT)} lean_commit differs from the manifest")
    return problems


def check_files(require_reviews, verify_pins, require_all):
    problems = []
    expected = []
    current_release = MANIFEST["history"][-1]["sha256"]
    for entry in MANIFEST["paper"]:
        directory = entry["dir"]
        relative = Path("papers") / directory
        folder = ROOT / relative
        archived = entry.get("archived", False)
        if not folder.is_dir():
            if archived or require_all:
                problems.append(f"Missing manuscript directory {relative}")
            continue
        required = ARCHIVED_FILES if archived else V2_FILES
        for name in required:
            if not (folder / name).is_file():
                problems.append(f"Missing {relative / name}")
        if not archived:
            for name in SUBMISSION_FILES:
                if not (folder / "submission" / name).is_file():
                    problems.append(f"Missing {relative / 'submission' / name}")
            if entry.get("supersedes") and not (folder / "CHANGES.md").is_file():
                problems.append(f"Missing {relative / 'CHANGES.md'}")
            problems.extend(check_metadata(entry, folder))
        if require_reviews:
            for reviewer in entry["reviews"]:
                report = ROOT / "papers" / "reviews" / entry.get("review_dir", directory) / f"{reviewer}.md"
                if not report.is_file():
                    problems.append(f"Missing {report.relative_to(ROOT)}")
        pdf = folder / "paper.pdf"
        if not pdf.is_file():
            continue
        data = pdf.read_bytes()
        if not data.startswith(b"%PDF-") or b"%%EOF" not in data[-1024:]:
            problems.append(f"Invalid PDF header or trailer in {relative}")
        if archived and digest_bytes(data) != current_release.get(directory):
            problems.append(f"Archived {relative / 'paper.pdf'} differs from {MANIFEST['history'][-1]['tag']}")
        if shutil.which("pdfinfo"):
            result = subprocess.run(["pdfinfo", str(pdf)], capture_output=True, text=True)
            if result.returncode or not re.search(r"^Pages:\s+[1-9][0-9]*$", result.stdout, re.M):
                problems.append(f"Poppler could not read {relative / 'paper.pdf'}")
        if verify_pins:
            problems.extend(check_pdf_pins(pdf))
        expected.append(f"{digest_bytes(data)}  {relative.as_posix()}/paper.pdf")
    return expected, problems


def check_history():
    """Each earlier release tag must still name its commit and its recorded PDF bytes."""
    problems = []
    for release in MANIFEST["history"]:
        tag = release["tag"]
        try:
            commit = git("rev-parse", f"{tag}^{{commit}}").strip()
        except ValueError:
            problems.append(f"Release tag {tag} is not available in this clone")
            continue
        if commit != release["commit"]:
            problems.append(f"Release tag {tag} points to {commit}, expected {release['commit']}")
            continue
        for directory, expected in release["sha256"].items():
            try:
                data = git("show", f"{commit}:papers/{directory}/paper.pdf", binary=True)
            except ValueError:
                problems.append(f"{tag} lacks papers/{directory}/paper.pdf")
                continue
            if digest_bytes(data) != expected:
                problems.append(f"{tag}: papers/{directory}/paper.pdf digest differs from the record")
    return problems


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-checksums", action="store_true",
                        help="record the current PDF hashes after rebuilding")
    parser.add_argument("--require-reviews", action="store_true",
                        help="require the independent reports and their disposition for each manuscript")
    parser.add_argument("--verify-pins", action="store_true",
                        help="check Lean source links embedded in PDFs against available Git history")
    parser.add_argument("--verify-history", action="store_true",
                        help="check that earlier release tags still identify their recorded PDFs")
    parser.add_argument("--require-all", action="store_true",
                        help="require every manuscript listed in papers/manifest.toml")
    args = parser.parse_args()
    if args.verify_pins and not shutil.which("pdfinfo"):
        parser.error("--verify-pins requires Poppler pdfinfo")
    lines, problems = check_files(args.require_reviews, args.verify_pins, args.require_all)
    if args.verify_history:
        problems.extend(check_history())
    manifest = ROOT / "papers" / "SHA256SUMS"
    content = "\n".join(lines) + "\n"
    if not problems and args.write_checksums:
        manifest.write_text(content, encoding="utf-8", newline="\n")
    elif not manifest.exists() or manifest.read_text(encoding="utf-8") != content:
        problems.append("papers/SHA256SUMS differs from the manuscript PDFs")
    if problems:
        raise SystemExit("\n".join(problems))
    print(f"Verified source companions and SHA-256 for {len(lines)} manuscripts.")


if __name__ == "__main__":
    main()
