# Building and checking the manuscripts

Each numbered directory contains the LaTeX source, bibliography, compiled PDF and a short guide to the claims that merit review. The public release includes the PDFs so that a reader can compare an archived paper with the exact Lean proof snapshot.

## Compile

Install TeX Live with pdfLaTeX, BibTeX, latexmk, the AMS classes, standard LaTeX packages and PGF/TikZ. For a Debian or Ubuntu environment the relevant packages are normally `latexmk`, `lmodern`, `texlive-latex-extra`, `texlive-pictures` and `texlive-fonts-recommended`. From the repository root:

```sh
papers/build.sh
```

To compile a single manuscript:

```sh
papers/build.sh 01-stoneham-polynomials
```

The script resolves cross-references and bibliographies through latexmk. It uses a temporary output directory for auxiliary files and copies the completed PDF into its manuscript directory. The release was prepared with TeX Live 2026. Font, engine and package versions can affect PDF serialization and pagination.

## Verify a downloaded release

```sh
sha256sum -c papers/SHA256SUMS
python3 -B papers/check_release.py --require-reviews
```

The checksums identify the archived files. In a Git clone containing the referenced commits, add `--verify-pins` to check the source file and line for each GitHub Lean link embedded in the PDFs. This option uses Poppler’s `pdfinfo`. After intentionally rebuilding a new version, inspect the PDFs and record their checksums with `python3 -B papers/check_release.py --write-checksums`. Consult each reviewer's guide for the declaration names and the precise status of the paper's mathematical inputs. [Manuscript index](README.md) · [Owner's DOI guide](ARCHIVING.md)
