#!/usr/bin/env python3
"""Structural check of CITATION.cff (Citation File Format 1.2.0), without third-party packages.

    python3 scripts/check_citation.py [path]

It parses the small YAML subset the file uses (top-level scalars, block lists of scalars, and a list of
author maps) and checks the keys, types and values the CFF 1.2.0 schema requires, plus the repository's own
rules: the only author is the approved one, and no ORCID, email or other identifying field appears.
When `cffconvert` is installed, run `cffconvert --validate` as well for a full schema validation.
"""

from __future__ import annotations

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
ALLOWED_KEYS = {"abstract", "authors", "cff-version", "commit", "contact", "date-released", "doi", "identifiers",
                "keywords", "license", "license-url", "message", "preferred-citation", "references",
                "repository", "repository-artifact", "repository-code", "title", "type", "url", "version"}
REQUIRED = ("cff-version", "message", "title", "authors")
AUTHOR_KEYS = {"family-names", "given-names", "affiliation"}  # ORCID, email and the like are not approved
APPROVED = {"family-names": "Anderson", "given-names": "Christopher", "affiliation": "Independent Researcher"}
SPDX = {"MIT", "Apache-2.0", "CC-BY-4.0", "CC-BY-SA-4.0"}


def scalar(text: str) -> str:
    text = text.strip()
    if len(text) >= 2 and text[0] == text[-1] and text[0] in "\"'":
        return text[1:-1]
    return text


def parse(text: str) -> dict:
    data: dict = {}
    key = None
    for n, raw in enumerate(text.splitlines(), 1):
        line = raw.rstrip()
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        if not line.startswith(" "):
            m = re.match(r"^([A-Za-z][\w-]*):(?:\s+(.*))?$", line)
            if not m:
                raise ValueError(f"line {n}: cannot parse {line!r}")
            key = m.group(1)
            if key in data:
                raise ValueError(f"line {n}: duplicate key {key}")
            data[key] = scalar(m.group(2)) if m.group(2) else []
            continue
        if key is None or not isinstance(data[key], list):
            raise ValueError(f"line {n}: unexpected indentation")
        stripped = line.strip()
        if stripped.startswith("- "):
            item = stripped[2:]
            m = re.match(r"^([A-Za-z][\w-]*):\s+(.*)$", item)
            data[key].append({m.group(1): scalar(m.group(2))} if m else scalar(item))
        else:
            m = re.match(r"^([A-Za-z][\w-]*):\s+(.*)$", stripped)
            if not m or not data[key] or not isinstance(data[key][-1], dict):
                raise ValueError(f"line {n}: cannot parse {line!r}")
            data[key][-1][m.group(1)] = scalar(m.group(2))
    return data


def check(data: dict) -> list[str]:
    errs = []
    for k in REQUIRED:
        if k not in data or data[k] in ("", []):
            errs.append(f"missing required key {k}")
    for k in data:
        if k not in ALLOWED_KEYS:
            errs.append(f"unknown key {k}")
    if data.get("cff-version") != "1.2.0":
        errs.append("cff-version must be 1.2.0")
    if data.get("type") not in ("software", "dataset"):
        errs.append("type must be software or dataset")
    authors = data.get("authors", [])
    if not isinstance(authors, list) or not all(isinstance(a, dict) for a in authors):
        errs.append("authors must be a list of maps")
    else:
        for a in authors:
            if not ({"family-names", "given-names"} <= set(a) or "name" in a):
                errs.append(f"author lacks family-names and given-names: {a}")
            extra = set(a) - AUTHOR_KEYS
            if extra:
                errs.append(f"author field not approved by the owner: {sorted(extra)}")
            for k, v in APPROVED.items():
                if a.get(k) != v:
                    errs.append(f"author {k} must be {v!r}")
        if len(authors) != 1:
            errs.append("exactly one approved author is expected")
    if not re.match(r"^https://github\.com/eldernos/MathematicsResearch$", str(data.get("repository-code", ""))):
        errs.append("repository-code must be the repository URL")
    if data.get("license") not in SPDX:
        errs.append(f"license must be an SPDX identifier, one of {sorted(SPDX)}")
    if not isinstance(data.get("keywords"), list) or not data["keywords"]:
        errs.append("keywords must be a nonempty list")
    version = data.get("version", "")
    if not version:
        errs.append("version is required for this repository")
    for k in ("url", "repository-code"):
        if k in data and not str(data[k]).startswith("https://"):
            errs.append(f"{k} must be an https URL")
    return errs


def main(argv=None) -> int:
    argv = sys.argv[1:] if argv is None else argv
    path = pathlib.Path(argv[0]) if argv else ROOT / "CITATION.cff"
    try:
        errs = check(parse(path.read_text(encoding="utf-8")))
    except (ValueError, OSError) as e:
        errs = [str(e)]
    for e in errs:
        print(f"error: {path.name}: {e}")
    if not errs:
        print(f"{path.name}: structure valid (CFF 1.2.0)")
    return 1 if errs else 0


if __name__ == "__main__":
    sys.exit(main())
