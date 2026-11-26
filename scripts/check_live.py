#!/usr/bin/env python3
"""Read-only check of the public pages: GitHub Pages and the alphaXiv records.

    python3 -B scripts/check_live.py [--base-url URL] [--no-alphaxiv] [--retries N]

For every current manuscript it fetches the deployed page and its same-directory PDF and compares the PDF's SHA-256
with ``papers/SHA256SUMS``. For every record in ``papers/alphaxiv-records.toml`` it fetches the alphaXiv page and PDF,
compares the title and the PDF digest, and prints the licence setting alphaXiv shows. A differing alphaXiv licence is a
WARNING for the owner to settle on alphaXiv (nothing here can change it); every other mismatch is an error (exit 1).
Nothing is posted anywhere, and nothing here says that any search engine lists these pages.
"""
import argparse
import hashlib
import html
import re
import sys
import time
import tomllib
import urllib.error
import urllib.request

import portal

ROOT = portal.ROOT
BASE_URL = "https://eldernos.github.io/MathematicsResearch/"
CC_BY = "creativecommons.org/licenses/by/4.0"


def fetch(url, retries=0):
    for attempt in range(retries + 1):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
            with urllib.request.urlopen(req, timeout=60) as r:
                return r.status, r.read()
        except urllib.error.HTTPError as e:
            status, body = e.code, b""
        except OSError:
            status, body = 0, b""
        if attempt < retries:
            time.sleep(5 * (attempt + 1))
    return status, body


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--base-url", default=BASE_URL)
    ap.add_argument("--no-alphaxiv", action="store_true")
    ap.add_argument("--retries", type=int, default=0)
    a = ap.parse_args(argv)
    base = a.base_url if a.base_url.endswith("/") else a.base_url + "/"
    sums = {}
    for line in (ROOT / "papers" / "SHA256SUMS").read_text(encoding="utf-8").splitlines():
        m = re.fullmatch(r"([0-9a-f]{64}) [ *](\S+)", line.strip())
        if m:
            sums[m.group(2)] = m.group(1)
    _, papers = portal.load_registry()
    records = {r["id"]: r for r in tomllib.loads(
        (ROOT / "papers" / "alphaxiv-records.toml").read_text(encoding="utf-8")).get("record", [])}
    errors, warnings = [], []

    for p in sorted((q for q in papers if q["current"]), key=portal.paper_key):
        slug = portal.dir_name(p["dir"])
        page = f"{base}papers/{slug}/"
        status, body = fetch(page, a.retries)
        text = body.decode("utf-8", "replace")
        if status != 200:
            errors.append(f"{page}: HTTP {status}")
            continue
        mid = str((p.get("metadata") or {}).get("id") or "")
        rec = records.get(mid)
        if rec and rec["alphaxiv"] not in text:
            errors.append(f"{page}: no link to {rec['alphaxiv']}")
        if not rec and "alphaxiv.org/abs/" in text:
            errors.append(f"{page}: alphaXiv link without a record")
        want = sums.get(f"{p['dir']}/paper.pdf")
        status, pdf = fetch(page + "paper.pdf", a.retries)
        if status != 200 or hashlib.sha256(pdf).hexdigest() != want:
            errors.append(f"{page}paper.pdf: HTTP {status}, digest "
                          f"{'matches' if status == 200 and hashlib.sha256(pdf).hexdigest() == want else 'differs'}")
        m = re.search(r'name="citation_pdf_url" content="([^"]*)"', text)
        if not m or m.group(1) != page + "paper.pdf":
            errors.append(f"{page}: citation_pdf_url is {m.group(1) if m else None}")
        print(f"checked {slug}")

    if not a.no_alphaxiv:
        for mid, rec in records.items():
            url = rec["alphaxiv"]
            title = next(p["title"] for p in papers if (p.get("metadata") or {}).get("id") == mid and p["current"])
            status, body = fetch(url, a.retries)
            text = body.decode("utf-8", "replace")
            m = re.search(r"<title>([^<]*)</title>", text)
            if status != 200 or not m or html.unescape(m.group(1)) != f"{title} | alphaXiv":
                errors.append(f"{url}: HTTP {status}, title {m.group(1) if m else None!r}")
            lic = re.search(r'license:"([^"]*)"', text)
            if not lic or CC_BY not in lic.group(1):
                warnings.append(f"{url}: licence shown is {lic.group(1) if lic else None} (repository: CC-BY-4.0)")
            d = next(v["dir"] for v in rec["versions"])
            status, pdf = fetch(url + ".pdf", a.retries)
            if status != 200 or hashlib.sha256(pdf).hexdigest() != sums.get(f"papers/{d}/paper.pdf"):
                errors.append(f"{url}.pdf: HTTP {status}, digest differs from papers/SHA256SUMS")
            print(f"checked alphaXiv {mid}")

    for w in warnings:
        print("WARNING:", w)
    for e in errors:
        print("ERROR:", e)
    print(f"{len(errors)} error(s), {len(warnings)} warning(s)")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
