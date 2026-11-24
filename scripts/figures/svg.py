"""Shared visual language for the repository figures.

Every figure is a standalone SVG written with the standard library only, so the
figures can be regenerated without third-party packages. Each figure is rendered
twice, once for a light page and once for a dark page. README pages select the
variant with a ``<picture>`` element.

Colour convention (identical in every figure)
--------------------------------------------
``normal``     aqua    -- normality, uniform distribution, D = 0
``resonance``  orange  -- persistent resonance, concentration, exact positive discrepancy
``barrier``    violet  -- an arithmetic barrier (for example exponential denominator growth)
``unresolved`` neutral grey with a 45 degree hatch -- open or uncertified conditions
``exact``      blue    -- neutral exact data (never shown together with ``barrier``)

At most three hues appear in one figure. Text is always drawn in ink colours,
never in a series colour, and every coloured region carries a direct label.
The palette was checked with the dataviz validator (all-pairs, both modes) for
the triples {normal, resonance, barrier} and {normal, resonance, exact}.

Layout standard
---------------
Canvas width 720 (``Svg(720, H, ...)``); GitHub scales figures to the column width,
so on a phone they shrink to about half size. Keep body text at 13 px or more,
headings at 18 px, at most about six labelled elements per panel, and no text
narrower than the canvas margins (24 px).

Provenance badges
-----------------
``theorem``     -- values are consequences of a stated theorem
``exact``       -- exact finite computation (rational arithmetic)
``illustration``-- numerical illustration; not evidence for any limit statement
"""

from __future__ import annotations

from dataclasses import dataclass
from html import escape
import math

FONT = ("-apple-system, BlinkMacSystemFont, 'Segoe UI', 'Noto Sans', Helvetica, "
        "Arial, sans-serif")


@dataclass(frozen=True)
class Theme:
    name: str
    surface: str
    panel: str
    ink: str
    ink2: str
    muted: str
    grid: str
    rule: str
    normal: str
    resonance: str
    barrier: str
    exact: str
    unresolved: str
    hatch: str


LIGHT = Theme(
    name="light", surface="#ffffff", panel="#f6f8fa", ink="#1f2328", ink2="#59636e",
    muted="#818b98", grid="#e3e6ea", rule="#c7ccd1",
    normal="#1baf7a", resonance="#eb6834", barrier="#6250d6", exact="#2a78d6",
    unresolved="#d0d4d9", hatch="#8a929b",
)

DARK = Theme(
    name="dark", surface="#0d1117", panel="#151b23", ink="#f0f6fc", ink2="#b7bdc8",
    muted="#8b949e", grid="#262c36", rule="#3d444d",
    normal="#199e70", resonance="#d95926", barrier="#9085e9", exact="#3987e5",
    unresolved="#3a414b", hatch="#7d8590",
)

THEMES = (LIGHT, DARK)

PROVENANCE = {
    "theorem": "Theorem consequence",
    "exact": "Exact finite computation",
    "illustration": "Numerical illustration · not evidence",
}


def fmt(x: float) -> str:
    """Compact, deterministic number formatting for SVG attributes."""
    if isinstance(x, int):
        return str(x)
    s = f"{x:.2f}".rstrip("0").rstrip(".")
    return "0" if s in ("-0", "") else s


class Svg:
    """A tiny deterministic SVG builder."""

    def __init__(self, width: int, height: int, theme: Theme, title: str, desc: str):
        self.w, self.h, self.t = width, height, theme
        self.parts: list[str] = []
        self.title, self.desc = title, desc

    # -- primitives -------------------------------------------------------
    def add(self, raw: str) -> None:
        self.parts.append(raw)

    def rect(self, x, y, w, h, fill="none", stroke="none", sw=1, rx=0, opacity=None, extra=""):
        op = f' fill-opacity="{fmt(opacity)}"' if opacity is not None else ""
        self.add(f'<rect x="{fmt(x)}" y="{fmt(y)}" width="{fmt(max(w, 0))}" height="{fmt(max(h, 0))}"'
                 f' rx="{fmt(rx)}" fill="{fill}" stroke="{stroke}" stroke-width="{fmt(sw)}"{op}{extra}/>')

    def line(self, x1, y1, x2, y2, stroke, sw=1, dash=None, extra=""):
        d = f' stroke-dasharray="{dash}"' if dash else ""
        self.add(f'<line x1="{fmt(x1)}" y1="{fmt(y1)}" x2="{fmt(x2)}" y2="{fmt(y2)}" stroke="{stroke}"'
                 f' stroke-width="{fmt(sw)}"{d}{extra}/>')

    def path(self, d, stroke="none", fill="none", sw=1, dash=None, extra=""):
        da = f' stroke-dasharray="{dash}"' if dash else ""
        self.add(f'<path d="{d}" fill="{fill}" stroke="{stroke}" stroke-width="{fmt(sw)}"'
                 f' stroke-linejoin="round" stroke-linecap="round"{da}{extra}/>')

    def polyline(self, pts, stroke, sw=2, fill="none", dash=None):
        d = "M" + " L".join(f"{fmt(x)} {fmt(y)}" for x, y in pts)
        self.path(d, stroke=stroke, fill=fill, sw=sw, dash=dash)

    def circle(self, cx, cy, r, fill, stroke="none", sw=1, opacity=None):
        op = f' fill-opacity="{fmt(opacity)}"' if opacity is not None else ""
        self.add(f'<circle cx="{fmt(cx)}" cy="{fmt(cy)}" r="{fmt(r)}" fill="{fill}" stroke="{stroke}"'
                 f' stroke-width="{fmt(sw)}"{op}/>')

    def text(self, x, y, s, size=12, fill=None, anchor="start", weight=None, italic=False,
             rotate=None, baseline=None):
        fill = fill or self.t.ink
        attrs = [f'x="{fmt(x)}"', f'y="{fmt(y)}"', f'font-size="{fmt(size)}"', f'fill="{fill}"']
        if anchor != "start":
            attrs.append(f'text-anchor="{anchor}"')
        if weight:
            attrs.append(f'font-weight="{weight}"')
        if italic:
            attrs.append('font-style="italic"')
        if baseline:
            attrs.append(f'dominant-baseline="{baseline}"')
        if rotate is not None:
            attrs.append(f'transform="rotate({fmt(rotate)} {fmt(x)} {fmt(y)})"')
        self.add(f'<text {" ".join(attrs)}>{s if s.startswith("<tspan") else escape(s)}</text>')

    def rich(self, x, y, runs, size=12, anchor="start", fill=None):
        """Text with italic runs: ``runs`` is a list of (string, italic) pairs."""
        fill = fill or self.t.ink
        spans = "".join(
            f'<tspan font-style="italic">{escape(s)}</tspan>' if it else f"<tspan>{escape(s)}</tspan>"
            for s, it in runs)
        a = f' text-anchor="{anchor}"' if anchor != "start" else ""
        self.add(f'<text x="{fmt(x)}" y="{fmt(y)}" font-size="{fmt(size)}" fill="{fill}"{a}>{spans}</text>')

    # -- composite elements ----------------------------------------------
    def hatch_rect(self, x, y, w, h, rx=0):
        """Unresolved region: neutral fill with a 45 degree hatch (texture, not hue)."""
        self.rect(x, y, w, h, fill=self.t.unresolved, rx=rx)
        self.rect(x, y, w, h, fill="url(#hatch)", rx=rx)

    def heading(self, title: str, subtitle: str | None = None, x=24, y=34):
        self.text(x, y, title, size=18, weight="600")
        if subtitle:
            self.text(x, y + 22, subtitle, size=13.5, fill=self.t.ink2)

    def badge(self, kind: str, x=None, y=20):
        """Provenance badge in the top-right corner."""
        label = PROVENANCE[kind]
        width = 7.3 * len(label) + 24
        x = self.w - 24 - width if x is None else x
        dash = ' stroke-dasharray="4 3"' if kind == "illustration" else ""
        self.add(f'<rect x="{fmt(x)}" y="{fmt(y)}" width="{fmt(width)}" height="22" rx="11"'
                 f' fill="{self.t.panel}" stroke="{self.t.rule}" stroke-width="1"{dash}/>')
        self.text(x + width / 2, y + 15.5, label, size=12.5, anchor="middle", fill=self.t.ink2)

    def swatch(self, x, y, kind: str, label: str, size=13):
        """Legend entry: a small square in a semantic colour followed by ink text."""
        if kind == "unresolved":
            self.hatch_rect(x, y - 10, 14, 14, rx=3)
        elif kind == "line":
            self.line(x, y - 3, x + 18, y - 3, self.t.ink2, sw=2)
        else:
            self.rect(x, y - 10, 14, 14, fill=getattr(self.t, kind), rx=3)
        self.text(x + (24 if kind == "line" else 20), y + 1, label, size=size, fill=self.t.ink2)

    def footer(self, s: str):
        self.text(24, self.h - 14, s, size=12, fill=self.t.muted)

    # -- axes -------------------------------------------------------------
    def axis_frame(self, x0, y0, x1, y1):
        self.line(x0, y1, x1, y1, self.t.rule)
        self.line(x0, y0, x0, y1, self.t.rule)

    def done(self) -> str:
        t = self.t
        head = (
            f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {self.w} {self.h}" '
            f'width="{self.w}" height="{self.h}" role="img" aria-labelledby="title desc" '
            f'font-family="{FONT}">\n'
            f'<title id="title">{escape(self.title)}</title>\n'
            f'<desc id="desc">{escape(self.desc)}</desc>\n'
            f'<defs><pattern id="hatch" width="6" height="6" patternUnits="userSpaceOnUse" '
            f'patternTransform="rotate(45)"><line x1="0" y1="0" x2="0" y2="6" stroke="{t.hatch}" '
            f'stroke-width="1.4"/></pattern></defs>\n'
            f'<rect width="{self.w}" height="{self.h}" rx="10" fill="{t.surface}"/>\n'
        )
        return head + "\n".join(self.parts) + "\n</svg>\n"


def log_scale(lo: float, hi: float, a: float, b: float):
    """Map [lo, hi] logarithmically onto pixel interval [a, b]."""
    llo, lhi = math.log(lo), math.log(hi)
    return lambda v: a + (math.log(v) - llo) / (lhi - llo) * (b - a)


def lin_scale(lo: float, hi: float, a: float, b: float):
    return lambda v: a + (v - lo) / (hi - lo) * (b - a)
