#!/usr/bin/env python3
"""Check the five archived manuscript PDFs and their source and review companions."""
import argparse
import hashlib
import re
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PAPERS = (
    "01-stoneham-polynomials",
    "02-localized-normality",
    "03-signed-resonance",
    "04-arithmetic-certificates",
    "05-classical-denominators",
)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_files(require_reviews):
    problems = []
    expected = []
    for directory in PAPERS:
        relative = Path("papers") / directory
        folder = ROOT / relative
        for name in ("paper.tex", "references.bib", "REVIEW.md", "paper.pdf"):
            if not (folder / name).is_file():
                problems.append(f"Missing {relative / name}")
        if require_reviews:
            for reviewer in ("gemini", "sonnet"):
                report = ROOT / "papers" / "reviews" / directory / f"{reviewer}.md"
                if not report.is_file():
                    problems.append(f"Missing {report.relative_to(ROOT)}")
        pdf = folder / "paper.pdf"
        if not pdf.is_file():
            continue
        data = pdf.read_bytes()
        if not data.startswith(b"%PDF-") or b"%%EOF" not in data[-1024:]:
            problems.append(f"Invalid PDF header or trailer in {relative}")
        if shutil.which("pdfinfo"):
            result = subprocess.run(["pdfinfo", str(pdf)], capture_output=True, text=True)
            if result.returncode or not re.search(r"^Pages:\s+[1-9][0-9]*$", result.stdout, re.M):
                problems.append(f"Poppler could not read {relative / 'paper.pdf'}")
        expected.append(f"{digest(pdf)}  {relative / 'paper.pdf'}")
    return expected, problems


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-checksums", action="store_true",
                        help="record the current PDF hashes after rebuilding")
    parser.add_argument("--require-reviews", action="store_true",
                        help="also require independent Gemini and Sonnet reports for each manuscript")
    args = parser.parse_args()
    lines, problems = check_files(args.require_reviews)
    manifest = ROOT / "papers" / "SHA256SUMS"
    content = "\n".join(lines) + "\n"
    if not problems and args.write_checksums:
        manifest.write_text(content, encoding="utf-8")
    elif not manifest.exists() or manifest.read_text(encoding="utf-8") != content:
        problems.append("papers/SHA256SUMS differs from the archived manuscript PDFs")
    if problems:
        raise SystemExit("\n".join(problems))
    print(f"Verified source companions and SHA-256 for {len(lines)} manuscript PDFs.")


if __name__ == "__main__":
    main()
