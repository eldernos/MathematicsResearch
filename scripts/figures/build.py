#!/usr/bin/env python3
"""Generate, or check, every repository figure and its underlying data.

    python3 scripts/figures/build.py            # write SVGs, data and figures.json
    python3 scripts/figures/build.py --check    # fail if any committed output is stale
    python3 scripts/figures/build.py --pdf      # also print vector PDFs for LaTeX (needs Chrome)

Each module ``scripts/figures/fig_*.py`` defines

    SLUG      file stem, for example "stoneham-square-lattice"
    META      dict with keys title, caption, alt, provenance, results, sources
    compute() deterministic data (exact arithmetic where the figure claims exactness)
    data_files(data) -> {file name: text} written to assets/figures/data/
    render(data, theme) -> SVG text

Outputs: ``assets/figures/<slug>-light.svg``, ``assets/figures/<slug>-dark.svg``,
``assets/figures/data/*`` and the metadata index ``assets/figures/figures.json``.
The PDF variants in ``assets/figures/pdf/`` are light-theme prints for manuscripts.
"""

from __future__ import annotations

import argparse
import importlib
import json
import pathlib
import shutil
import subprocess
import sys
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent.parent
OUT = ROOT / "assets" / "figures"
sys.path.insert(0, str(HERE))
sys.dont_write_bytecode = True

import svg  # noqa: E402

REQUIRED_META = ("number", "title", "caption", "alt", "provenance", "results", "sources")


def modules():
    mods = []
    for path in sorted(HERE.glob("fig_*.py")):
        mod = importlib.import_module(path.stem)
        missing = [k for k in REQUIRED_META if k not in mod.META]
        if missing:
            raise SystemExit(f"{path.name}: META lacks {missing}")
        if mod.META["provenance"] not in svg.PROVENANCE:
            raise SystemExit(f"{path.name}: unknown provenance {mod.META['provenance']!r}")
        mods.append(mod)
    mods.sort(key=lambda m: m.META["number"])
    return mods


def outputs() -> dict[pathlib.Path, str]:
    files: dict[pathlib.Path, str] = {}
    index = []
    for mod in modules():
        data = mod.compute()
        names = []
        for name, text in sorted(mod.data_files(data).items()):
            files[OUT / "data" / name] = text
            names.append(f"assets/figures/data/{name}")
        variants = {}
        for theme in svg.THEMES:
            path = OUT / f"{mod.SLUG}-{theme.name}.svg"
            files[path] = mod.render(data, theme)
            variants[theme.name] = path.relative_to(ROOT).as_posix()
        entry = dict(mod.META)
        entry.update(slug=mod.SLUG, light=variants["light"], dark=variants["dark"],
                     pdf=f"assets/figures/pdf/{mod.SLUG}.pdf",
                     script=f"scripts/figures/{mod.__name__}.py", data=names)
        index.append(entry)
    files[OUT / "figures.json"] = json.dumps(index, indent=2, ensure_ascii=False) + "\n"
    return files


def print_pdfs(index_entries) -> None:
    chrome = shutil.which("google-chrome") or shutil.which("chromium") or shutil.which("chromium-browser")
    if not chrome:
        raise SystemExit("PDF export needs google-chrome or chromium on PATH")
    (OUT / "pdf").mkdir(parents=True, exist_ok=True)
    for entry in index_entries:
        src = (ROOT / entry["light"]).read_text()
        head = src.split(">", 1)[0]
        width = float(head.split('width="')[1].split('"')[0])
        height = float(head.split('height="')[1].split('"')[0])
        html = (f"<!doctype html><html><head><meta charset='utf-8'><style>@page{{size:{width}px {height}px;"
                f"margin:0}}html,body{{margin:0;padding:0}}svg{{display:block}}</style></head><body>"
                f"{src}</body></html>")
        with tempfile.TemporaryDirectory() as tmp:
            page = pathlib.Path(tmp) / "figure.html"
            page.write_text(html)
            target = ROOT / entry["pdf"]
            subprocess.run([chrome, "--headless=new", "--disable-gpu", "--no-pdf-header-footer",
                            f"--user-data-dir={tmp}/profile", f"--print-to-pdf={target}", page.as_uri()],
                           check=True, capture_output=True)
        print(f"wrote {entry['pdf']}")


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--check", action="store_true", help="verify committed outputs instead of writing")
    ap.add_argument("--pdf", action="store_true", help="also export light-theme PDFs with headless Chrome")
    args = ap.parse_args(argv)
    files = outputs()
    if args.check:
        stale = [p for p, text in files.items() if not p.exists() or p.read_text() != text]
        expected = {p for p in files}
        extra = [p for p in OUT.glob("*.svg") if p not in expected]
        extra += [p for p in (OUT / "data").glob("*") if p not in expected]
        for p in stale:
            print(f"stale or missing: {p.relative_to(ROOT)}")
        for p in extra:
            print(f"not produced by any generator: {p.relative_to(ROOT)}")
        if stale or extra:
            print("Run python3 scripts/figures/build.py")
            return 1
        pdfs = [p for p in json.loads(files[OUT / "figures.json"]) if not (ROOT / p["pdf"]).exists()]
        for p in pdfs:
            print(f"missing PDF export (run with --pdf): {p['pdf']}")
        print(f"{sum(1 for p in files if p.suffix == '.svg')} figure variants and their data are current.")
        return 1 if pdfs else 0
    for path, text in files.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        if not path.exists() or path.read_text() != text:
            path.write_text(text)
            print(f"wrote {path.relative_to(ROOT)}")
    if args.pdf:
        print_pdfs(json.loads(files[OUT / "figures.json"]))
    return 0


if __name__ == "__main__":
    sys.exit(main())
