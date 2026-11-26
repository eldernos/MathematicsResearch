# Publishing pipeline

This page describes how a research result moves from a research phase to a public preprint. The steps that change only the repository are automated. Every step that publishes or makes a public record runs only when the owner explicitly triggers or approves it.

| Stage | What happens | Where | Automated? |
| --- | --- | --- | --- |
| 1. Research phase | Notes, proofs, Lean modules and exact scripts on a `research/phase-N-*` branch, closed by a `research-checkpoint-N` tag | `notes/phaseN/`, `NormalityChecker/`, `scripts/` | CI: [Lean verification](../.github/workflows/lean.yml) on every push |
| 2. Manuscript | A paper directory with `paper.tex`, `metadata.toml`, `VERIFICATION.md`, `LEDGER.md` and `submission/`, following the [contract](../papers/WAVE2-CONTRACT.md) | `papers/NN-name/` | CI: [manuscript verification](../.github/workflows/manuscripts.yml) rebuilds every PDF twice and checks pins, metadata and earlier releases |
| 3. Review | At least one independent model review from a different provider than the writer, plus a resolution record. First-batch papers get two. | `papers/reviews/NN-name/` | `check_release.py --require-reviews` enforces their presence |
| 4. Release | Rebuild the PDFs, `check_release.py --write-checksums`, `release_manifest.py`, then tag `manuscripts-vX.Y.Z` and publish a GitHub release with the PDFs, the manifest and the checksums | `papers/SHA256SUMS`, `papers/RELEASES.md` | Owner approves the tag and release |
| 5. Landing pages | `scripts/site.py` builds one page per manuscript, with Highwire `citation_*` tags and schema.org JSON-LD | [site](site.md), [pages workflow](../.github/workflows/pages.yml) | Deploys on pushes to `main` once Pages is enabled |
| 6. alphaXiv | [`scripts/alphaxiv_publish.py`](../scripts/alphaxiv_publish.py) uploads the recorded PDF and calls `publish_paper` with the structured AI disclosure | [workflow](../.github/workflows/alphaxiv.yml), `papers/NN-name/submission/alphaxiv.toml` | Manual dispatch only, gated by the `alphaxiv` environment's required reviewer |
| 7. Record | Add the returned alphaXiv URL to [`papers/alphaxiv-records.toml`](../papers/alphaxiv-records.toml). Later versions are then posted with `new_version_of`, which keeps one alphaXiv record per paper. | repository | Owner commits the record |

## alphaXiv specifics

alphaXiv documents an MCP server at `https://api.alphaxiv.org/mcp/v1` (Streamable HTTP). For scripts and CI it accepts a personal API key from *Settings > MCP/API*, sent as `Authorization: Bearer <key>`. Publishing has two steps. `get_upload_instructions` returns an upload command (PDF, at most 50 MB) that answers with a `pdfId`. `publish_paper` then takes `pdf_id`, optional `title`, `abstract`, `authors`, `url_slug` or `new_version_of`, and the required `ai_disclosure`. That disclosure rates idea, literature, experiments, analysis and writing as `ai`, `mixed` or `human`, and lists up to ten tools with model, harness and contribution. The call returns `published` with a URL, `rejected` with a reason, or `in_review`. Licence and subject category are not API parameters; set them in the alphaXiv web form. One submission per account can be in progress at a time, so the workflow serializes runs. Every submission is screened, and screening is not peer review. [alphaXiv MCP documentation](https://www.alphaxiv.org/docs/mcp) · [Submission policy](https://www.alphaxiv.org/docs/submission-policy) · [Policy review](../papers/submission/POLICIES.md)

### Safeguards

- **Dry run by default.** It contacts no one. It prints the exact `publish_paper` arguments, including disclosure metadata that the owner has not yet confirmed, with a warning.
- **Owner confirmation and submission state.** An actual submission is refused until the owner sets `owner_confirmed = true` in the paper's `submission/alphaxiv.toml` *on the default branch*. Release content (the PDF, checksum and metadata) comes from the tag, while the confirmation, the AI disclosure and the alphaXiv records are read from `origin/main`. So they can be updated after tagging without moving the tag.
- **Approved release only.** `--publish` needs `--release <tag>`. The tag must be the release named in `papers/manifest.toml`, the checkout must be exactly the tagged commit with a clean tree, and the PDF must match `papers/SHA256SUMS` *at that tag*. The workflow checks out `refs/tags/<release>`, without persisted credentials.
- **Credential destinations.** The API key is sent only to `https` hosts under `alphaxiv.org`, on the default port and without embedded credentials. An upload destination elsewhere, for example a presigned storage URL, receives no credentials. Redirects are refused, so a request carrying the key is never forwarded.
- **No shell interpolation.** The server's curl instructions are parsed, never executed. Workflow inputs reach the shell only through environment variables and are validated against fixed patterns first.
- **Persistent identifiers.** Records are keyed by the manuscript's permanent identifier (`id` in `metadata.toml`). A recorded manuscript is posted with `new_version_of`, which keeps its alphaXiv URL across revisions and directory changes, and a version already recorded is never resubmitted.
- **Compatibility.** alphaXiv's Cloudflare front end rejects the default Python User-Agent (error 1010), so the script sends its own. With it, an unauthenticated request receives `401` with `WWW-Authenticate: Bearer realm="mcp"`, which confirms the endpoint and the authentication scheme. The authenticated tool schemas, and the upload address that `get_upload_instructions` returns at run time, have not yet been exercised. For the first real submission, run a dry run, then publish one paper while watching the result.
- **Independent review.** The pipeline was reviewed by a model from a different provider before any key existed: [report](../papers/submission/PIPELINE-REVIEW.md) · [resolution](../papers/submission/PIPELINE-REVIEW-RESOLUTION.md).

## One-time owner setup

1. Create an alphaXiv API key under *Settings > MCP/API*.
2. In GitHub, open *Settings > Environments*, create `alphaxiv`, add yourself as a required reviewer, restrict *Deployment branches and tags* to the default branch (`main`), and add the secret `ALPHAXIV_API_KEY`.
3. Enable Pages with *Settings > Pages > Source: GitHub Actions* ([site guide](site.md)).
4. For each paper, review `submission/alphaxiv.toml` and set `owner_confirmed = true`.

## Publishing a manuscript

1. Make sure the release tag exists and `papers/SHA256SUMS` at that tag lists the PDF. The script refuses any PDF that the checksum file does not record.
2. Run the *Publish to alphaXiv* workflow with `publish` unchecked and read the printed request.
3. Run it again with `publish` checked and approve the environment gate.
4. Commit the returned URL to `papers/alphaxiv-records.toml`.

For a local run instead of CI, `python3 -B scripts/alphaxiv_publish.py papers/<dir>` prints the request. On a clean checkout of the release tag, `--publish --release manuscripts-v2.0.0` with `ALPHAXIV_API_KEY` set submits it.
