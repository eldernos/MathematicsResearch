# Independent Security and Compatibility Review: alphaXiv Publishing Pipeline

- **Reviewer model:** Gemini 4 Argon (Antigravity)
- **Date:** 2026-11-25
- **Reviewed commit:** `34d16d9e771d85239c9476b48e087b5747107649` (`publication/wave-2`)
- **Notice:** AI model review; not a professional security audit.

## Verdict

**Hold before creating an alphaXiv API key or tagging `manuscripts-v2.0.0` (3 High, 3 Medium, 1 Low findings).**

The pipeline's core design is well-structured: shell execution of server-supplied upload instructions has been replaced with pure-Python `urllib` requests, GitHub Actions workflow inputs are passed exclusively through validated environment variables without `${{ ... }}` shell interpolation, `actions/checkout` is SHA-pinned with `persist-credentials: false`, and live unauthenticated probing of `https://api.alphaxiv.org/mcp/v1` confirms that the server uses stateless Streamable HTTP (`WWW-Authenticate: Bearer realm="mcp"`, no `Mcp-Session-Id`) and accepts `MCP-Protocol-Version: 2025-06-18` with the script's explicit `User-Agent`.

However, three high-severity issues should be fixed before minting a live `ALPHAXIV_API_KEY` or cutting the `manuscripts-v2.0.0` tag:
1. Python's default `urllib.request.HTTPRedirectHandler` automatically follows `301`/`302`/`303` redirects on `POST` requests and forwards the `Authorization: Bearer <key>` header verbatim to cross-host or `http://` redirect targets.
2. Checking out the immutable release tag `refs/tags/<release>` with a clean working tree creates a lifecycle deadlock for `papers/alphaxiv-records.toml` (which is updated on `main` *after* the tag is created and published), making post-tag publication records invisible during subsequent runs at that tag.
3. Three manuscripts (`01-stoneham-polynomials-v2`, `02-localized-normality-v2`, and `06-multiplicative-lambert`) have directory names (including `-v2`) as their `id` in `metadata.toml`, conflicting with `papers/manifest.toml`, `docs/registry/papers.toml`, and the `id = "VI"` example in `papers/alphaxiv-records.toml`.

---

## Requirement-by-Requirement Verification

| # | Owner Requirement | Status | Assessment |
| --- | --- | --- | --- |
| 1 | Authenticated publication possible only from an approved release commit (`papers/manifest.toml` `release`, exact tagged commit checked out, clean tree, PDF matching `papers/SHA256SUMS` at tag) | **Pass (with lifecycle caveat)** | `check_release()` and `check_pdf(paper_dir, args.release)` in [`scripts/alphaxiv_publish.py`](../../scripts/alphaxiv_publish.py#L123-L150) verify that `--release` equals `manifest.toml` `release` and matches `manuscripts-v\d+\.\d+\.\d+`, that `refs/tags/<release>^{commit}` equals `HEAD`, that `git status --porcelain --untracked-files=no` is empty, and that `paper.pdf` matches `git show <release>:papers/SHA256SUMS`. See Finding 2 for how strict tag checkout interacts with post-tag updates to `papers/alphaxiv-records.toml` and `owner_confirmed`. |
| 2 | No unsafe shell interpolation in workflow or script (no shell execution of server-supplied `curl` command) | **Pass** | [`.github/workflows/alphaxiv.yml`](../../.github/workflows/alphaxiv.yml#L42-L89) passes `inputs.release`, `inputs.paper`, and `secrets.ALPHAXIV_API_KEY` exclusively via `env:` bindings and validates `$RELEASE` and `$PAPER` against strict regexes before use. [`scripts/alphaxiv_publish.py`](../../scripts/alphaxiv_publish.py#L63-L68) invokes `git` with argument lists (`shell=False`) and parses `get_upload_instructions` with `shlex.split` without executing a shell. |
| 3 | Credentials only reach validated destinations (host matching, suffix tricks, userinfo, IDN, uppercase, ports, redirects) | **Partial fail (Finding 1, Finding 5)** | `trusted_host()` correctly blocks suffix tricks (`alphaxiv.org.evil.com`, `evilalphaxiv.org`), non-`https` schemes, `https://api.alphaxiv.org@evil.com` userinfo host confusion, and Cyrillic/IDN homoglyphs in the `alphaxiv.org` suffix. However, `urllib.request.urlopen()` follows HTTP redirects by default and copies `Authorization: Bearer <key>` to any cross-host or `http://` redirect destination (Finding 1). `trusted_host()` also permits arbitrary ports and userinfo on trusted hosts (Finding 5). |
| 4 | Future revisions use persistent manuscript identifiers (records keyed by metadata `id`; `new_version_of`; refusal to resubmit a recorded version) | **Fail (Finding 2, Finding 3)** | The code logic in `find_record()`, `build_request()`, and `check_release()` keys records by `meta["id"]`, attaches `new_version_of`, and refuses recorded versions. In practice, three `metadata.toml` files store directory names (`01-stoneham-polynomials-v2`, `02-localized-normality-v2`, `06-multiplicative-lambert`) instead of permanent identifiers, and post-tag commits to `papers/alphaxiv-records.toml` are not present at `refs/tags/<release>`. |
| 5 | Dry run lets owner inspect unconfirmed disclosure metadata; actual publication requires `owner_confirmed = true` | **Pass locally / Caveat in CI (Finding 2)** | Running `python3 -B scripts/alphaxiv_publish.py papers/06-multiplicative-lambert` locally succeeds without contacting alphaXiv, validates `paper.pdf` against `papers/SHA256SUMS`, prints the full JSON payload with `"owner_confirmed": false`, and emits the stderr warning. Passing `--publish` immediately raises `Refusal` when `owner_confirmed` is false. In CI, the `dry-run` job also checks out `refs/tags/${{ inputs.release }}`, so it cannot run before the release tag exists. |
| 6 | Live API compatibility (`initialize` / session header, SSE & JSON response handling, `publish_paper` parsing, multipart upload construction) | **Partial pass (Finding 4, Finding 6)** | Documentation at `https://www.alphaxiv.org/docs/mcp` and live unauthenticated probing confirm that `https://api.alphaxiv.org/mcp/v1` is stateless ("Streamable HTTP without sessions... The server issues no `Mcp-Session-Id`"), supports `MCP-Protocol-Version: 2025-06-18`, and requires no prior `initialize` handshake or session header. However, the regex and `-F`/`-H` parser in `upload()` and the single-line SSE / JSON output parsers in `post_json()` and `main()` are brittle against valid server responses (Findings 4 and 6). |

---

## Numbered Findings

### Finding 1 (High): `urllib.request.urlopen` follows redirects and leaks `Authorization: Bearer <key>` to untrusted hosts or plaintext `http://`

- **Severity:** High
- **Location:** [`scripts/alphaxiv_publish.py`](../../scripts/alphaxiv_publish.py#L152-L160) (`post_json`) and [`scripts/alphaxiv_publish.py`](../../scripts/alphaxiv_publish.py#L201-L209) (`upload`)
- **Problem:** Both `post_json()` and `upload()` check `trusted_host(url)` on the initial URL before attaching `"Authorization": f"Bearer {key}"` to `urllib.request.Request`, and then call `urllib.request.urlopen(...)`. In Python's standard library, `urllib.request.HTTPRedirectHandler.redirect_request()` automatically follows `301`, `302`, and `303` responses on `POST` requests (converting them to `GET`) and copies every request header except `Content-Length` and `Content-Type` into the redirected `Request`:
  ```python
  CONTENT_HEADERS = ("content-length", "content-type")
  newheaders = {k: v for k, v in req.headers.items()
                if k.lower() not in CONTENT_HEADERS}
  ```
  Unlike `requests` or `httpx`, Python's `HTTPRedirectHandler` **does not strip `Authorization` on cross-host redirects or `https` → `http` scheme downgrades** (verified by unit test `test_redirect_handler_forwards_authorization_by_default` in [`scripts/test_alphaxiv_publish.py`](../../scripts/test_alphaxiv_publish.py#L43-L58)). If `get_upload_instructions` returns an upload URL on `https://api.alphaxiv.org/...` that redirects (`302`/`303`) to an external object-storage host (such as S3, GCS, or R2), or if any `*.alphaxiv.org` endpoint redirects off-domain, `urllib` silently forwards `Authorization: Bearer <key>` to the external destination.
- **Concrete fix:** Install a no-redirect opener (or a redirect handler that refuses cross-host and non-HTTPS redirects for authenticated requests) and use it in place of `urllib.request.urlopen`:
  ```diff
  --- a/scripts/alphaxiv_publish.py
  +++ b/scripts/alphaxiv_publish.py
  @@ -55,6 +55,13 @@ class Refusal(SystemExit):
       pass
   
   
  +class _NoRedirect(urllib.request.HTTPRedirectHandler):
  +    def redirect_request(self, req, fp, code, msg, headers, newurl):
  +        raise Refusal(f"refusing HTTP {code} redirect from {req.full_url} to {newurl}")
  +
  +
  +_OPENER = urllib.request.build_opener(_NoRedirect)
  +
   def load_toml(path: Path) -> dict:
  ```
  Then replace `urllib.request.urlopen(...)` at lines 158 and 207 with `_OPENER.open(...)`.

---

### Finding 2 (High): Tag-checkout lifecycle deadlock hides post-tag updates to `papers/alphaxiv-records.toml` and blocks pre-tag CI dry runs

- **Severity:** High
- **Location:** [`scripts/alphaxiv_publish.py`](../../scripts/alphaxiv_publish.py#L86-L90), [`scripts/alphaxiv_publish.py`](../../scripts/alphaxiv_publish.py#L137-L150), [`.github/workflows/alphaxiv.yml`](../../.github/workflows/alphaxiv.yml#L49-L89), [`docs/publishing-pipeline.md`](../../docs/publishing-pipeline.md#L21-L35)
- **Problem:**
  1. `check_release()` requires that `HEAD` equal `refs/tags/{release}^{commit}` and that `git status --porcelain --untracked-files=no` be empty; correspondingly, `.github/workflows/alphaxiv.yml` checks out `ref: refs/tags/${{ inputs.release }}`.
  2. A paper in `manuscripts-v2.0.0` cannot be published until the tag `refs/tags/manuscripts-v2.0.0` exists, and release tags are never moved ([`papers/release_manifest.py`](../../papers/release_manifest.py#L78)). Therefore, when the owner follows step 4 of [`docs/publishing-pipeline.md`](../../docs/publishing-pipeline.md#L33) (*"Commit the returned URL to `papers/alphaxiv-records.toml`"*), that commit is made on `main` *after* the commit tagged `manuscripts-v2.0.0`.
  3. On any subsequent run of `.github/workflows/alphaxiv.yml` (or local `--publish --release manuscripts-v2.0.0` checked out at the tag), `load_toml(RECORDS)` reads `papers/alphaxiv-records.toml` from the tagged commit—where `papers/alphaxiv-records.toml` is still empty. Consequently, `find_record(meta)` returns `None`, and the duplicate-submission guard (`if record and any(v.get("version") == meta["version"] ...): raise Refusal(...)`) never fires for papers recorded after the release tag was created.
  4. In addition, the `dry-run` job in [`.github/workflows/alphaxiv.yml`](../../.github/workflows/alphaxiv.yml#L49-L53) also checks out `ref: refs/tags/${{ inputs.release }}`. If the owner runs the CI dry run before tagging `manuscripts-v2.0.0`, `actions/checkout` fails because the tag does not exist yet; if the owner tags `manuscripts-v2.0.0` first while `owner_confirmed = false` in `submission/alphaxiv.toml`, then `owner_confirmed = false` is frozen inside the tag and the `publish` job can never succeed at that tag.
- **Concrete fix:**
  1. In `scripts/alphaxiv_publish.py`, add an optional `--records <path>` argument (defaulting to `papers/alphaxiv-records.toml`) and also union records from `git show refs/remotes/origin/main:papers/alphaxiv-records.toml` and `git show refs/heads/main:papers/alphaxiv-records.toml` when those refs exist locally, so post-tag publication records on `main` are always enforced even when `HEAD` is at `refs/tags/<release>`.
  2. In `.github/workflows/alphaxiv.yml`, let `dry-run` check out `ref: ${{ inputs.release }}` (or fall back to `github.ref` when the tag does not exist yet), and in `publish` read `papers/alphaxiv-records.toml` from `origin/main` before checking out the tag (or fetch `origin/main` so `git show refs/remotes/origin/main:papers/alphaxiv-records.toml` is available):
  ```diff
  --- a/scripts/alphaxiv_publish.py
  +++ b/scripts/alphaxiv_publish.py
  @@ -86,10 +86,23 @@ def manuscript(paper_dir: Path) -> tuple[dict, dict]:
   
   
   def find_record(meta: dict) -> dict | None:
  -    for record in load_toml(RECORDS).get("record", []):
  -        if record.get("id") == meta["id"]:
  -            return record
  -    return None
  +    sources = [load_toml(RECORDS)]
  +    for ref in ("refs/remotes/origin/main", "refs/heads/main"):
  +        probe = subprocess.run(["git", "show", f"{ref}:papers/alphaxiv-records.toml"],
  +                               cwd=ROOT, capture_output=True, text=True)
  +        if probe.returncode == 0 and probe.stdout.strip():
  +            sources.append(tomllib.loads(probe.stdout))
  +    merged: dict | None = None
  +    seen_versions: set[str] = set()
  +    for data in sources:
  +        for record in data.get("record", []):
  +            if record.get("id") == meta["id"]:
  +                if merged is None:
  +                    merged = {"id": meta["id"], "alphaxiv": record.get("alphaxiv"), "versions": []}
  +                elif not merged.get("alphaxiv") and record.get("alphaxiv"):
  +                    merged["alphaxiv"] = record["alphaxiv"]
  +                for v in record.get("versions", []):
  +                    if v.get("version") not in seen_versions:
  +                        seen_versions.add(v.get("version"))
  +                        merged["versions"].append(v)
  +    return merged
  ```

---

### Finding 3 (High): Inconsistent and version-coupled `id` fields across `papers/*/metadata.toml`, `papers/manifest.toml`, `docs/registry/papers.toml`, and `papers/alphaxiv-records.toml`

- **Severity:** High
- **Location:** [`papers/01-stoneham-polynomials-v2/metadata.toml`](../../papers/01-stoneham-polynomials-v2/metadata.toml#L1), [`papers/02-localized-normality-v2/metadata.toml`](../../papers/02-localized-normality-v2/metadata.toml#L1), [`papers/06-multiplicative-lambert/metadata.toml`](../../papers/06-multiplicative-lambert/metadata.toml#L1), [`papers/alphaxiv-records.toml`](../../papers/alphaxiv-records.toml#L7-L10), [`papers/check_release.py`](../../papers/check_release.py#L81-L97), [`scripts/portal.py`](../../scripts/portal.py#L791-L826)
- **Problem:** `scripts/alphaxiv_publish.py` keys `papers/alphaxiv-records.toml` by `meta["id"]` (`metadata.toml` `id`) specifically so that a revision in a new directory (such as `*-v2` or `*-v3`) shares a permanent identifier with earlier versions and is submitted with `new_version_of`. Across the 10 current manuscripts, however, three `metadata.toml` files store the directory name—including `-v2`—as `id`, and the identifier scheme disagrees across the repository's four tables:

  | Manuscript directory | `docs/registry/papers.toml` `number` | `papers/manifest.toml` `id` | `papers/<dir>/metadata.toml` `id` | `papers/alphaxiv-records.toml` comment |
  | --- | --- | --- | --- | --- |
  | `01-stoneham-polynomials-v2` | `"I"` | `"B"` (v1.1: `"I"`) | `"01-stoneham-polynomials-v2"` | — |
  | `02-localized-normality-v2` | `"II"` | `"E"` (v1.1: `"II"`) | `"02-localized-normality-v2"` | — |
  | `03-signed-resonance-v1.2` | `"III"` | `"III"` (v1.1: `"III"`) | `"III"` | — |
  | `04-arithmetic-certificates-v2` | `"IV"` | `"G"` (v1.1: `"IV"`) | `"G"` | — |
  | `05-classical-denominators-v2` | `"V"` | `"F"` (v1.1: `"V"`) | `"F"` | — |
  | `06-multiplicative-lambert` | `"VI"` | `"A"` | `"06-multiplicative-lambert"` | `id = "VI"` |
  | `07-synthetic-expansions` | `"VII"` | `"C"` | `"C"` | — |
  | `08-stoneham-product-orbits` | `"VIII"` | `"D"` | `"D"` | — |
  | `09-erdos-borwein-note` | `"IX"` | `"EB"` | `"EB"` | — |
  | `10-discrepancy-arithmetic` | `"X"` | `"H"` | `"H"` | — |

  In particular:
  - In [`papers/alphaxiv-records.toml`](../../papers/alphaxiv-records.toml#L7-L10), the template entry for `06-multiplicative-lambert` gives `id = "VI"`, whereas [`papers/06-multiplicative-lambert/metadata.toml`](../../papers/06-multiplicative-lambert/metadata.toml#L1) has `id = "06-multiplicative-lambert"` (verified by running the dry run for `papers/06-multiplicative-lambert`, which outputs `"manuscript": "06-multiplicative-lambert"`). If the owner uncomments the template entry with `id = "VI"`, `find_record(meta)` will not match it.
  - In `01-stoneham-polynomials-v2` and `02-localized-normality-v2`, `id` embeds `-v2`, which is tied to the versioned directory name rather than a permanent manuscript ID.
  - Neither [`papers/check_release.py`](../../papers/check_release.py#L81-L97) (`check_metadata`) nor [`scripts/portal.py`](../../scripts/portal.py#L791-L826) (`validate_metadata`) checks that `metadata.toml` `id` matches `papers/manifest.toml` `id` or `docs/registry/papers.toml` `number`.
- **Concrete fix:** Align `id` across all `papers/*/metadata.toml` files (and `papers/manifest.toml` or `docs/registry/papers.toml`) to one permanent identifier per manuscript series (e.g., the Roman numerals `"I"` through `"X"` from `docs/registry/papers.toml` `number`, which remain invariant across `v1.1` → `v2.0` → `v3.0` and match the `id = "VI"` template in `papers/alphaxiv-records.toml`), and enforce consistency in `papers/check_release.py` and `scripts/portal.py`:
  ```diff
  --- a/papers/check_release.py
  +++ b/papers/check_release.py
  @@ -90,6 +90,8 @@ def check_metadata(entry, folder):
       for key in METADATA_KEYS:
           if key not in data:
               problems.append(f"{path.relative_to(ROOT)} lacks `{key}`")
  +    if str(data.get("id", "")) != entry["id"]:
  +        problems.append(f"{path.relative_to(ROOT)} id {data.get('id')!r} differs from the manifest ({entry['id']!r})")
       if str(data.get("version", "")) != entry["version"]:
           problems.append(f"{path.relative_to(ROOT)} version {data.get('version')!r} differs from the manifest")
  ```

---

### Finding 4 (Medium): `upload()` instruction parser is brittle against Markdown code fences, multiple `-F` form fields, and non-allowlisted headers

- **Severity:** Medium
- **Location:** [`scripts/alphaxiv_publish.py`](../../scripts/alphaxiv_publish.py#L52), [`scripts/alphaxiv_publish.py`](../../scripts/alphaxiv_publish.py#L179-L207)
- **Problem:** As noted in [`docs/publishing-pipeline.md`](../../docs/publishing-pipeline.md#L19), the upload instructions parser has not yet been exercised against a live `get_upload_instructions` response. Four parsing hazards exist in `upload()`:
  1. **Markdown code fences / trailing prose:** `re.search(r"curl\s.+?(?=\n\s*\n|\Z)", instructions, re.S)` stops only at a blank line (`\n\s*\n`) or end of string. If `get_upload_instructions` wraps the command in a Markdown code block (` ```bash\ncurl ...\n``` `) without a blank line before the closing fence, or places a single newline between the `curl` command and the reminder prose (which the docs describe as *"a curl command ... and a reminder to ask the operator"*), `match.group(0)` captures the closing ```` ``` ```` and/or prose. Any apostrophe in the captured prose (e.g., `user's` or `don't`) causes `shlex.split` to crash with `ValueError: No closing quotation`, or leaves ```` ``` ```` tokens in `argv`.
  2. **Multiple `-F` form fields:** `elif arg in ("-F", "--form"): field = argv[i + 1].split("=", 1)[0]` overwrites `field` on every `-F` flag and drops all non-file form fields. If the upload endpoint uses a presigned multipart POST (e.g., S3/GCS policy fields `-F "key=..." -F "policy=..." -F "file=@..."`), all non-file form fields are lost.
  3. **Header allowlist and duplicate `Content-Type`:** `FORWARDED_HEADERS = {"content-type", "x-upload-token", "x-pdf-upload-token"}` silently drops any other custom header required by the upload endpoint (e.g., `x-api-key` or `x-amz-*`). Conversely, if the instructions include `-H "content-type: ..."` in lowercase, `headers["content-type"]` is populated at line 198 and `headers["Content-Type"]` is added at line 206, creating duplicate keys in the case-sensitive `headers` dictionary.
  4. **Unsanitized `field` in multipart boundary header:** `field` is interpolated directly into `Content-Disposition: form-data; name="{field}"` without checking for `"` or CR/LF characters.
- **Concrete fix:**
  ```diff
  --- a/scripts/alphaxiv_publish.py
  +++ b/scripts/alphaxiv_publish.py
  @@ -181,7 +181,10 @@ def upload(pdf: Path, key: str) -> str:
       """Interpret the server's curl instructions without running them, and upload the PDF with urllib."""
       instructions = tool("get_upload_instructions", {}, key)
  -    match = re.search(r"curl\s.+?(?=\n\s*\n|\Z)", instructions, re.S)
  +    normalized = instructions.replace("\r\n", "\n")
  +    fenced = re.search(r"```(?:bash|sh|shell)?\s*\n(curl\s.+?)\n```", normalized, re.S)
  +    match = fenced or re.search(r"(curl\s(?:[^\n\\]|\\\n)+)", normalized)
       if not match:
  -        raise Refusal(f"no upload command in the instructions:\n{instructions}")
  -    argv = shlex.split(match.group(0).replace("\\\n", " "))
  +        raise Refusal("no upload command found in get_upload_instructions response")
  +    cmd_text = match.group(1).replace("\\\n", " ")
  +    argv = shlex.split(cmd_text)
       urls = [a for a in argv if re.match(r"https?://", a)]
       if len(urls) != 1:
  -        raise Refusal(f"expected one upload URL, found {urls}")
  +        raise Refusal(f"expected one upload URL, found {len(urls)}")
       url = urls[0]
       if urllib.parse.urlsplit(url).scheme != "https":
  -        raise Refusal(f"refusing a non-https upload URL: {url}")
  +        raise Refusal("refusing a non-https upload URL")
       headers = {"User-Agent": USER_AGENT}
       field = "file"
  +    extra_fields: list[tuple[str, str]] = []
       for i, arg in enumerate(argv[:-1]):
           if arg in ("-H", "--header"):
               name, _, value = argv[i + 1].partition(":")
  -            if name.strip().lower() in FORWARDED_HEADERS:
  +            lname = name.strip().lower()
  +            if lname != "content-type" and (lname in FORWARDED_HEADERS or lname.startswith("x-")):
                   headers[name.strip()] = value.strip()
           elif arg in ("-F", "--form"):
  -            field = argv[i + 1].split("=", 1)[0]
  +            fname, _, fval = argv[i + 1].partition("=")
  +            if not re.fullmatch(r"[A-Za-z0-9_.-]+", fname):
  +                raise Refusal(f"unsafe multipart field name: {fname!r}")
  +            if fval.startswith("@"):
  +                field = fname
  +            else:
  +                extra_fields.append((fname, fval))
       if trusted_host(url):
           headers["Authorization"] = f"Bearer {key}"   # the key goes only to alphaxiv.org hosts
       boundary = uuid.uuid4().hex
  -    body = (f"--{boundary}\r\nContent-Disposition: form-data; name=\"{field}\"; filename=\"{pdf.name}\"\r\n"
  -            "Content-Type: application/pdf\r\n\r\n").encode() + pdf.read_bytes() + f"\r\n--{boundary}--\r\n".encode()
  +    parts = [
  +        f"--{boundary}\r\nContent-Disposition: form-data; name=\"{k}\"\r\n\r\n{v}\r\n".encode()
  +        for k, v in extra_fields
  +    ]
  +    parts.append(
  +        (f"--{boundary}\r\nContent-Disposition: form-data; name=\"{field}\"; filename=\"{pdf.name}\"\r\n"
  +         "Content-Type: application/pdf\r\n\r\n").encode() + pdf.read_bytes() + f"\r\n--{boundary}--\r\n".encode()
  +    )
  +    body = b"".join(parts)
       headers["Content-Type"] = f"multipart/form-data; boundary={boundary}"
  ```

---

### Finding 5 (Medium): `trusted_host()` permits non-443 ports, userinfo, and leading-dot subdomain labels

- **Severity:** Medium
- **Location:** [`scripts/alphaxiv_publish.py`](../../scripts/alphaxiv_publish.py#L70-L73)
- **Problem:** `trusted_host(url)` checks:
  ```python
  def trusted_host(url: str) -> bool:
      parts = urllib.parse.urlsplit(url)
      host = (parts.hostname or "").lower()
      return parts.scheme == "https" and (host == TRUSTED_SUFFIX or host.endswith("." + TRUSTED_SUFFIX))
  ```
  While this properly rejects `https://alphaxiv.org.evil.com`, `https://evilalphaxiv.org`, `https://api.alphaxiv.org@evil.com`, non-HTTPS schemes, and IDN homoglyphs in `alphaxiv.org`:
  - It ignores `parts.port`, allowing credentials to be sent to arbitrary ports on any subdomain (e.g., `https://sub.alphaxiv.org:8443/`), and does not trigger `parts.port` validation (so `https://api.alphaxiv.org:badport/` returns `True` from `trusted_host`).
  - It ignores `parts.username` and `parts.password` (allowing `https://user:pass@api.alphaxiv.org/` or parser-differential backslash URLs such as `https://evil.com\@api.alphaxiv.org/`).
  - It accepts leading dots or non-ASCII characters in subdomain labels (`https://.alphaxiv.org/`, `https://..alphaxiv.org/`).
- **Concrete fix:**
  ```diff
  --- a/scripts/alphaxiv_publish.py
  +++ b/scripts/alphaxiv_publish.py
  @@ -70,4 +70,12 @@ def git(*args: str) -> str:
   def trusted_host(url: str) -> bool:
  +    if "\\" in url:
  +        return False
       parts = urllib.parse.urlsplit(url)
  +    try:
  +        port = parts.port
  +    except ValueError:
  +        return False
       host = (parts.hostname or "").lower()
  -    return parts.scheme == "https" and (host == TRUSTED_SUFFIX or host.endswith("." + TRUSTED_SUFFIX))
  +    return (parts.scheme == "https" and not parts.username and not parts.password and port in (None, 443)
  +            and bool(re.fullmatch(r"(?:[a-z0-9](?:[a-z0-9-]*[a-z0-9])?\.)*alphaxiv\.org", host)))
  ```

---

### Finding 6 (Medium): SSE event parsing in `post_json()`, JSON result parsing in `main()`, and `HTTPError` diagnostics lack resilience for long-running Streamable HTTP calls

- **Severity:** Medium
- **Location:** [`scripts/alphaxiv_publish.py`](../../scripts/alphaxiv_publish.py#L152-L177), [`scripts/alphaxiv_publish.py`](../../scripts/alphaxiv_publish.py#L248-L260)
- **Problem:**
  1. **SSE parsing in `post_json()`:** alphaXiv's MCP documentation specifies that responses return as a server-sent event stream (`text/event-stream`) and that `publish_paper` waits up to ~80 seconds for automated screening. `post_json()` extracts `events = [line[5:].strip() for line in text.splitlines() if line.startswith("data:")]` and parses only `json.loads(events[-1])`. If the SSE stream contains a multi-line `data:` payload for one event, a trailing server notification/ping event, or a closing `data: [DONE]` frame, `events[-1]` either fails `json.loads()` or returns a notification lacking `"result"`, causing `message["result"]` in `tool()` to raise `KeyError`.
  2. **`publish_paper` result parsing in `main()`:** `tool()` joins all `content` text items with `"\n"`. If `publish_paper` returns multiple text parts (e.g., JSON plus human-readable guidance) or wraps the JSON in Markdown fences, `json.loads(response)` fails, `outcome` becomes `{"raw": response}`, and line 258 (`if outcome.get("status") not in ("published", "in_review"): raise Refusal(...)`) exits with an error *after the paper has already been submitted*.
  3. **Opaque `HTTPError` crashes:** Neither `post_json()` nor `upload()` catches `urllib.error.HTTPError`, so an HTTP 400/401/429/500 response prints a stack trace without the server's JSON error body (and could dump internal frame state if tracebacks are inspected).
- **Concrete fix:** Reassemble SSE events per event block (`\n\n`), select the JSON-RPC message matching the request `id` (or carrying `"result"` / `"error"`), extract fenced or embedded JSON objects if top-level `json.loads(response)` fails, and wrap `_OPENER.open(...)` in `try ... except urllib.error.HTTPError as err` to raise a clean `Refusal(f"HTTP {err.code} from {url}")`.

---

### Finding 7 (Low): Record validation edge cases, missing `url_slug` length check, workflow job timeouts, and environment branch-restriction docs

- **Severity:** Low
- **Location:** [`scripts/alphaxiv_publish.py`](../../scripts/alphaxiv_publish.py#L113-L120), [`scripts/alphaxiv_publish.py`](../../scripts/alphaxiv_publish.py#L184-L191), [`.github/workflows/alphaxiv.yml`](../../.github/workflows/alphaxiv.yml#L38-L89), [`docs/publishing-pipeline.md`](../../docs/publishing-pipeline.md#L21-L35)
- **Problem:**
  1. **Record without `alphaxiv` URL falls back to `url_slug`:** In `build_request()` (lines 114–117), `if record and record.get("alphaxiv"): args["new_version_of"] = record["alphaxiv"] elif sub.get("url_slug"): args["url_slug"] = sub["url_slug"]`. If a record exists in `papers/alphaxiv-records.toml` for `meta["id"]` with an empty or missing `alphaxiv` field (for example, if an earlier submission ended in `"status": "in_review"` without a final URL yet), `build_request()` silently falls through to `url_slug` and submits a brand-new duplicate entry instead of refusing.
  2. **Missing `url_slug` length/format check and non-strict `owner_confirmed` type check:** alphaXiv documents `url_slug` as `string (max 120)` and `title`/`abstract` as minimum length 1 (`1-500`, `1-10000`). `build_request()` checks upper bounds on `title`, `abstract`, and `authors`, but does not check `len(args["url_slug"]) <= 120` or non-emptiness of `title`/`abstract`. It also checks `bool(sub.get("owner_confirmed", False))` rather than `sub.get("owner_confirmed") is True` (in Python, `bool("false")` is `True`).
  3. **Potential token leakage in `upload()` error messages:** If `upload()` fails to parse `get_upload_instructions`, lines 184, 188, and 191 print the raw `instructions` or `urls` to stderr (`raise Refusal(f"no upload command in the instructions:\n{instructions}")`). While GitHub Actions masks `secrets.ALPHAXIV_API_KEY`, it does **not** mask dynamically generated upload tokens or presigned URL query strings returned by `get_upload_instructions`.
  4. **Missing `timeout-minutes` in `.github/workflows/alphaxiv.yml` and deployment branch rules in `docs/publishing-pipeline.md`:** Neither the `dry-run` job nor the `publish` job sets `timeout-minutes:`, defaulting to 360 minutes while holding the `alphaxiv` concurrency lock (`cancel-in-progress: false`). In [`docs/publishing-pipeline.md`](../../docs/publishing-pipeline.md#L24), step 2 of "One-time owner setup" instructs the owner to create the `alphaxiv` environment with a required reviewer, but does not instruct them to restrict **Deployment branches and tags** on that environment to `manuscripts-v*` tags / `main`.
- **Concrete fix:**
  - In `build_request()`, raise `Refusal` if `record is not None and not record.get("alphaxiv")`, enforce `sub.get("owner_confirmed") is True`, and check `1 <= len(args["title"]) <= 500`, `1 <= len(args["abstract"]) <= 10000`, and `len(args.get("url_slug", "")) <= 120`.
  - Redact query strings and header values from `upload()` `Refusal` messages (see Finding 4 patch).
  - Add `timeout-minutes: 10` to `dry-run` and `timeout-minutes: 15` to `publish` in `.github/workflows/alphaxiv.yml`, and document restricting the `alphaxiv` GitHub Environment to `manuscripts-v*` tags in `docs/publishing-pipeline.md`.

---

## Dry-Run and Test Verification Summary

1. **Dry run of `papers/06-multiplicative-lambert`:**
   - Executed `python3 -B scripts/alphaxiv_publish.py papers/06-multiplicative-lambert`.
   - Verified that it makes no network calls, validates `papers/06-multiplicative-lambert/paper.pdf` against `papers/SHA256SUMS`, outputs the complete JSON payload (`owner_confirmed: false`, `title`, normalized `abstract`, `authors: ["Christopher Anderson"]`, all 5 `ai_disclosure.stages`, 4 `ai_disclosure.tools` entries, and `url_slug: "disjunctive-nonnormal-multiplicative-lambert-series"`), and prints the expected unconfirmed-disclosure warning to stderr.
   - Observed `"manuscript": "06-multiplicative-lambert"` in the dry-run output, confirming Finding 3.
2. **Live read-only endpoint check (`https://api.alphaxiv.org/mcp/v1`):**
   - Verified without credentials that `POST https://api.alphaxiv.org/mcp/v1` with the script's `User-Agent` and `MCP-Protocol-Version: 2025-06-18` traverses Cloudflare and returns HTTP 401 `{"error":{"message":"Missing Authorization"}}` with `WWW-Authenticate: Bearer realm="mcp"`.
3. **Unit test suite ([`scripts/test_alphaxiv_publish.py`](../../scripts/test_alphaxiv_publish.py)):**
   - Added 11 unit tests covering `trusted_host()` (valid hosts, non-HTTPS schemes, suffix/prefix tricks, userinfo host confusion, IDN homoglyphs), `HTTPRedirectHandler` cross-host `Authorization` forwarding (Finding 1 reproduction), `build_request()` disclosure validation and `new_version_of` switching, `check_pdf()` checksum verification, `check_release()` tag/commit/clean-tree/duplicate-version guards, and `upload()` non-HTTPS refusal and external-host credential withholding.
