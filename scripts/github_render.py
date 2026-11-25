#!/usr/bin/env python3
"""Preview Markdown pages as GitHub renders them, and check their mathematics.

    python3 scripts/github_render.py OUTDIR README.md docs/results.md ...

This is a maintainer tool, not part of ``scripts/verify.sh``: it needs the GitHub CLI
(``gh``, authenticated), network access and Google Chrome or Chromium.

For each page it

1. renders the Markdown with GitHub's own GFM renderer (``POST /markdown`` with the
   repository as context), which produces the same HTML and ``<math-renderer>``
   containers that github.com serves;
2. wraps the HTML in GitHub's Markdown stylesheet, in a light and a dark variant,
   rewrites repository-relative image paths to local files and selects the matching
   ``<picture>`` source for each theme;
3. typesets every math container with MathJax 3, as github.com does in the browser,
   and renders Mermaid diagrams;
4. loads each variant in headless Chrome at desktop (1280 px) and phone (390 px)
   widths, saves screenshots, and reports MathJax errors, unrendered TeX commands,
   unbalanced braces, math wider than the phone viewport, images without alt text
   and Mermaid failures.

A math container in the HTML alone does not show that its contents typeset; step 3
and the reported checks do.
"""

from __future__ import annotations

import html
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
REPO = "eldernos/MathematicsResearch"
CSS = "https://cdnjs.cloudflare.com/ajax/libs/github-markdown-css/5.5.1/github-markdown-{}.min.css"
MATHJAX = "https://cdn.jsdelivr.net/npm/mathjax@3.2.2/es5/tex-svg.js"
MERMAID = "https://cdn.jsdelivr.net/npm/mermaid@10.9.1/dist/mermaid.min.js"

PROBE = r"""
<script>
window.__report = {done:false};
async function finish(){
  try { await MathJax.startup.promise; await MathJax.typesetPromise(); } catch(e) { window.__report.mathjax_exception = String(e); }
  try { await mermaid.run({querySelector: 'pre[lang="mermaid"], .mermaid'}); } catch(e) { window.__report.mermaid = String(e); }
  const r = window.__report;
  const containers = [...document.querySelectorAll('math-renderer')];
  r.math = containers.length;
  r.errors = containers.filter(c => c.querySelector('[data-mjx-error], mjx-merror')).map(c => c.getAttribute('data-src'));
  r.unrendered = containers.filter(c => !c.querySelector('mjx-container')).map(c => c.textContent.slice(0,120));
  const vw = document.documentElement.clientWidth;
  r.wide = containers.filter(c => { const m = c.querySelector('mjx-container svg'); return m && m.getBoundingClientRect().width > vw - 32; })
                     .map(c => c.getAttribute('data-src'));
  const text = document.querySelector('.markdown-body').innerText;
  r.literal_tex = (text.match(/\\[a-zA-Z]+/g) || []).filter(x => !['\\n','\\t'].includes(x)).slice(0,20);
  r.noalt = [...document.querySelectorAll('img')].filter(i => !i.alt).map(i => i.src).slice(0,10);
  r.broken_img = [...document.querySelectorAll('img')].filter(i => i.complete && i.naturalWidth === 0).map(i => i.src).slice(0,10);
  r.scroll_overflow = document.documentElement.scrollWidth > vw + 1;
  r.done = true;
  document.title = 'DONE ' + JSON.stringify(r);
}
window.addEventListener('load', () => setTimeout(finish, 50));
</script>
"""


def render_gfm(markdown: str) -> str:
    req = json.dumps({"text": markdown, "mode": "gfm", "context": REPO})
    out = subprocess.run(["gh", "api", "-X", "POST", "/markdown", "--input", "-"], input=req,
                         capture_output=True, text=True, encoding="utf-8", check=True)
    return out.stdout


def localize(body: str, page: pathlib.Path, theme: str) -> str:
    base = page.parent

    def fix(m):
        attr, url = m.group(1), m.group(2)
        if re.match(r"^[a-z]+:|^#|^//", url):
            return m.group(0)
        target = (base / html.unescape(url.split("#")[0])).resolve()
        return f'{attr}="{target.as_uri()}"'

    body = re.sub(r'(src|srcset)="([^"]+)"', fix, body)
    # choose the theme-appropriate <picture> source the way github.com does
    def pick(m):
        block = m.group(0)
        dark = re.search(r'<source media="\(prefers-color-scheme: dark\)" srcset="([^"]+)"', block)
        img = re.search(r'<img[^>]*>', block).group(0)
        if theme == "dark" and dark:
            img = re.sub(r'src="[^"]+"', f'src="{dark.group(1)}"', img)
        return img
    body = re.sub(r"<picture>.*?</picture>", pick, body, flags=re.S)
    # store the TeX source for the report, as github.com keeps it in the element
    body = re.sub(r"<math-renderer([^>]*)>(.*?)</math-renderer>",
                  lambda m: f'<math-renderer{m.group(1)} data-src="{html.escape(html.unescape(m.group(2)))}">{m.group(2)}</math-renderer>',
                  body, flags=re.S)
    return body


def page_html(body: str, theme: str) -> str:
    bg = "#0d1117" if theme == "dark" else "#ffffff"
    return f"""<!doctype html><html><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<link rel="stylesheet" href="{CSS.format(theme)}">
<style>body{{background:{bg};margin:0}} .markdown-body{{box-sizing:border-box;max-width:980px;margin:0 auto;padding:24px 16px}}
math-renderer.js-display-math{{display:block;overflow-x:auto}}</style>
<script>window.MathJax={{tex:{{inlineMath:[['$','$']],displayMath:[['$$','$$']]}},svg:{{fontCache:'global'}},startup:{{typeset:false}}}};</script>
<script src="{MATHJAX}"></script><script src="{MERMAID}"></script>
<script>mermaid.initialize({{startOnLoad:false, theme:'{"dark" if theme == "dark" else "default"}'}});</script>
{PROBE}</head><body><article class="markdown-body">{body}</article></body></html>"""


def chrome():
    exe = (os.environ.get("CHROME") or shutil.which("google-chrome") or shutil.which("chromium")
           or shutil.which("chromium-browser") or shutil.which("chrome")
           or next((c for c in ("C:/Program Files/Google/Chrome/Application/chrome.exe",
                                "C:/Program Files (x86)/Google/Chrome/Application/chrome.exe") if pathlib.Path(c).exists()), None))
    if not exe:
        raise SystemExit("needs google-chrome or chromium (or set CHROME to its path)")
    return exe


def run_page(html_file: pathlib.Path, width: int, shot: pathlib.Path, profile: str):
    # mermaid.min.js expects <pre lang="mermaid"> content as text; GitHub's API emits a
    # <pre lang="mermaid"> block, which mermaid.run() can process directly.
    cmd = [chrome(), "--headless=new", "--disable-gpu", f"--user-data-dir={profile}", "--hide-scrollbars",
           f"--window-size={width},2000", "--virtual-time-budget=20000", "--run-all-compositor-stages-before-draw"]
    dom = subprocess.run(cmd + ["--dump-dom", html_file.as_uri()], capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=180).stdout
    m = re.search(r"<title>DONE (.*?)</title>", dom, flags=re.S)
    report = json.loads(html.unescape(m.group(1))) if m else {"done": False}
    subprocess.run(cmd + [f"--screenshot={shot}", html_file.as_uri()], capture_output=True, timeout=180)
    return report


def main(argv):
    if len(argv) < 2:
        print(__doc__)
        return 2
    out = pathlib.Path(argv[0]).resolve()
    out.mkdir(parents=True, exist_ok=True)
    failures = 0
    with tempfile.TemporaryDirectory() as profile:
        for name in argv[1:]:
            page = (ROOT / name).resolve()
            md = page.read_text(encoding="utf-8")
            raw = render_gfm(md)
            # GitHub serves Mermaid as <pre lang="mermaid"><code>; give mermaid.js its plain text
            raw = re.sub(r'<pre lang="mermaid"[^>]*><code>(.*?)</code></pre>',
                         lambda m: f'<pre class="mermaid">{m.group(1)}</pre>', raw, flags=re.S)
            stem = name.replace("/", "_").removesuffix(".md")
            for theme in ("light", "dark"):
                f = out / f"{stem}-{theme}.html"
                f.write_text(page_html(localize(raw, page, theme), theme), encoding="utf-8")
                for width in (1280, 390):
                    rep = run_page(f, width, out / f"{stem}-{theme}-{width}.png", profile)
                    bad = {k: v for k, v in rep.items()
                           if k in ("errors", "unrendered", "wide", "literal_tex", "noalt", "broken_img",
                                    "mermaid", "mathjax_exception") and v}
                    if rep.get("scroll_overflow"):
                        bad["horizontal_scroll"] = True
                    if not rep.get("done"):
                        bad["incomplete"] = True
                    status = "ok" if not bad else "PROBLEMS"
                    failures += bool(bad)
                    print(f"{name} [{theme}, {width}px]: {rep.get('math', 0)} math containers, {status}"
                          + ("" if not bad else f" {json.dumps(bad, ensure_ascii=False)}"))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
