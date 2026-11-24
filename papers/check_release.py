#!/usr/bin/env python3
"""Check the five archived manuscript PDFs and their source and review companions."""
import argparse
from functools import lru_cache
import hashlib
import re
from pathlib import Path
import shutil
import subprocess
from urllib.parse import unquote, urlsplit

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


@lru_cache(maxsize=None)
def source_lines(revision, name):
    result = subprocess.run(["git", "show", f"{revision}:{name}"], cwd=ROOT,
                            capture_output=True, text=True)
    if result.returncode:
        raise ValueError(f"Missing source object {revision}:{name}")
    return result.stdout.splitlines()


def check_pdf_pins(pdf):
    """Validate the exact Git objects and line anchors embedded in the PDF annotations."""
    result = subprocess.run(["pdfinfo", "-url", str(pdf)], capture_output=True, text=True)
    if result.returncode:
        return [f"Cannot read PDF annotations from {pdf.name}"]
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


def check_files(require_reviews, verify_pins):
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
        if verify_pins:
            problems.extend(check_pdf_pins(pdf))
        expected.append(f"{digest(pdf)}  {relative / 'paper.pdf'}")
    return expected, problems


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-checksums", action="store_true",
                        help="record the current PDF hashes after rebuilding")
    parser.add_argument("--require-reviews", action="store_true",
                        help="also require independent Gemini and Sonnet reports for each manuscript")
    parser.add_argument("--verify-pins", action="store_true",
                        help="check Lean source links embedded in PDFs against available Git history")
    args = parser.parse_args()
    if args.verify_pins and not shutil.which("pdfinfo"):
        parser.error("--verify-pins requires Poppler pdfinfo")
    lines, problems = check_files(args.require_reviews, args.verify_pins)
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
