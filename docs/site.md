# Research landing site

The repository can publish a small static site: an index page and one page per current manuscript, with the title, author line, abstract, keywords, MSC2020 classification, download links, a BibTeX entry, the version history and links to the verification map. The site is generated from the same metadata as the README table, so it does not drift from it.

**Expected address:** <https://eldernos.github.io/MathematicsResearch/> (the address is not live until the owner enables Pages as described below).

## How the owner enables it

1. Merge the branch that contains [.github/workflows/pages.yml](../.github/workflows/pages.yml) into `main`.
2. In the repository on GitHub open **Settings → Pages**. Under **Build and deployment**, set **Source** to **GitHub Actions**.
3. Run the workflow **Research site** from the **Actions** tab (**Run workflow**), or push to `main`. The workflow tests the generator, checks that `papers/BIBLIOGRAPHY.bib` is current, builds the site in strict mode, and deploys it with `actions/deploy-pages`.
4. Open the address above and check one manuscript page: the PDF link, the BibTeX block and the version history.
5. Optionally set the repository homepage ([repository-metadata.md](repository-metadata.md)).

Before step 2 the deploy job fails with a message that Pages is not enabled. That is expected and harmless; the build job still validates the site.

## Build it locally

```sh
python3 scripts/site.py build            # writes site/ (git-ignored)
python3 scripts/site.py build --strict   # also fails if a manuscript lacks metadata.toml or paper.pdf
python3 scripts/site.py bib              # regenerates papers/BIBLIOGRAPHY.bib
python3 -B scripts/test_site.py          # unit tests
```

Open `site/index.html` in a browser. The pages use no JavaScript, external fonts, analytics or trackers, adapt to narrow screens and to a dark colour scheme, and have a skip link and landmark regions.

## Where the data come from

| Page content | Source |
| --- | --- |
| Manuscript list, versions, status, supersession | [docs/registry/papers.toml](registry/papers.toml) |
| Title, abstract, keywords, MSC2020 codes, registry identifiers | `metadata.toml` in each manuscript directory, validated by `python3 scripts/portal.py check` |
| Paper III (version 1.1, retained) | `papers.toml`, because its archived directory is never edited |
| PDF links | `https://raw.githubusercontent.com/eldernos/MathematicsResearch/<tag>/<dir>/paper.pdf`, with the file on the `main` branch as a fallback until the release tag exists |
| Version history | the release tags `manuscripts-v1.0.0`, `manuscripts-v1.1.0` and `manuscripts-v2.0.0`; earlier PDFs stay unchanged at their tags |
| Dates | `date` in `metadata.toml` if present, else the last commit that touched the manuscript directory |

## Author information

The v2 manuscripts and their pages show "Christopher Anderson · Independent Researcher". No ORCID, email address or other affiliation appears, and the issue tracker is the only contact route. The archived v1.1 PDFs carry no author line, so the page of Paper III (retained at version 1.1) says so and emits no author metadata. A named-author edition of the v1.1 papers would need a new version identifier ([licensing-proposal.md](licensing-proposal.md)).

## Indexing

Each manuscript page carries Highwire Press `citation_*` meta tags (`citation_title`, `citation_author`, `citation_publication_date`, `citation_pdf_url`, `citation_keywords`) and schema.org `ScholarlyArticle` JSON-LD. These describe the page in the formats that scholarly indexers read. **Nothing here submits the site anywhere, and nothing guarantees that Google Scholar, any other index or any search engine will list it.** Services apply their own inclusion rules, and a page that is only a landing page for a PDF hosted on GitHub may not qualify. Do not describe the manuscripts as indexed unless a search service actually lists them.

All pages state that the manuscripts are preprint drafts, that cross-model review is not independent human peer review, and that the Lean kernel checks only the declarations listed in each verification map.
