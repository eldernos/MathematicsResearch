"""Figure 5: exact discrepancy of three signed binary expansions before and after
translation by 1/3.

The values are the kernel-verified constants of ``binary_three_periods`` and
``translated_third_examples``. ``compute`` re-derives them from the periodic
shell recurrence with exact rational arithmetic and checks the product formula
D(mX + 1/3) = D(X) · D(1/3) with D(1/3) = 2/3.
"""

from __future__ import annotations

from fractions import Fraction as F

from svg import Svg, lin_scale

SLUG = "translated-discrepancy"
META = {
    "number": 5,
    "summary": 'Translation by 1/3 multiplies each exact discrepancy by 2/3, the discrepancy of the orbit of 1/3 (DS-03).',
    "title": "Exact discrepancy before and after rational translation",
    "caption": (
        "For the binary signed Stoneham expansions with *p* = 3 and phase words 1110, 10 and 100, "
        "the limiting interval discrepancy equals the upper density of zero-phase shells: 27/40, 3/4 "
        "and 12/13. Translating by 1/3 multiplies each value by the discrepancy 2/3 of the orbit of 1/3, "
        "giving 9/20, 1/2 and 8/13 for every nonzero integer multiple *m*. All six values are "
        "kernel-verified. The translated numbers remain nonnormal; translation lowers the discrepancy "
        "without removing the resonance."
    ),
    "alt": (
        "Dot plot on a horizontal discrepancy axis from 0 to 1. Three rows, one per phase word. In each "
        "row a filled orange dot marks the original discrepancy (27/40, 3/4, 12/13) and an open orange "
        "ring marks the translated discrepancy (9/20, 1/2, 8/13), joined by an arrow pointing left. "
        "A teal tick at zero marks normality."
    ),
    "provenance": "theorem",
    "results": ["DS-02", "DS-03"],
    "sources": [
        "NormalityChecker.SignedPhases.binary_three_periods",
        "NormalityChecker.SignedPhases.translated_third_examples",
        "notes/translated-shells.md",
    ],
}

WORDS = ["1110", "10", "100"]
P = 3
SHIFT = F(2, 3)  # interval discrepancy of the binary orbit of 1/3 (third_discrepancy_sharp)
LEAN = {"1110": (F(27, 40), F(9, 20)), "10": (F(3, 4), F(1, 2)), "100": (F(12, 13), F(8, 13))}


def periodic_discrepancy(word: str, p: int = P) -> F:
    """Upper density of zero-shell positions for a periodic phase word.

    With z_j = 1 on zero shells, H_{j+1} = (H_j + (p - 1) z_j) / p is the density at the
    end of shell j. Iterating once around the period gives an affine map with an exact
    fixed point; the upper density is the largest stationary value.
    """
    L = len(word)
    z = [1 if ch == "0" else 0 for ch in word]
    # H_L = H_0 / p^L + c; stationary H_0 = c / (1 - p^-L)
    c = F(0)
    for j in range(L):
        c = (c + (p - 1) * z[j]) / p
    h = c / (1 - F(1, p ** L))
    best = h
    for j in range(L):
        h = (h + (p - 1) * z[j]) / p
        best = max(best, h)
    return best


def compute():
    rows = []
    for w in WORDS:
        d = periodic_discrepancy(w)
        t = d * SHIFT
        assert (d, t) == LEAN[w], (w, d, t)
        rows.append({"word": w, "original": d, "translated": t})
    return {"rows": rows, "factor": SHIFT}


def data_files(data):
    lines = ["phase_word,discrepancy,translated_by_one_third,factor"]
    for r in data["rows"]:
        lines.append(f"{r['word']},{r['original']},{r['translated']},{data['factor']}")
    return {"translated-discrepancy.csv": "\n".join(lines) + "\n"}


def render(data, t):
    W, H = 720, 420
    s = Svg(W, H, t, META["title"], META["alt"])
    s.heading("Rational translation scales exact discrepancy",
              "Binary signed expansions with p = 3, translated by X ↦ mX + 1/3 for any nonzero integer m")
    s.badge("theorem", y=60)
    x0, x1 = 170, W - 60
    X = lin_scale(0, 1, x0, x1)
    top, row_h = 128, 62
    bottom = top + row_h * len(data["rows"]) - 20
    for k in range(0, 11):
        v = k / 10
        s.line(X(v), top - 18, X(v), bottom, t.grid)
        if k % 2 == 0:
            s.text(X(v), bottom + 20, f"{v:g}", size=11.5, anchor="middle", fill=t.ink2)
    s.text((x0 + x1) / 2, bottom + 42, "limiting interval discrepancy D", size=12, anchor="middle",
           fill=t.ink2)
    # normality reference at zero
    s.line(X(0), top - 18, X(0), bottom, t.normal, sw=3)
    s.text(X(0) + 6, top - 24, "normal: D = 0", size=11.5, fill=t.ink2)
    for i, r in enumerate(data["rows"]):
        y = top + i * row_h + 12
        s.text(x0 - 18, y - 2, f"phase word {r['word']}", size=12.5, anchor="end")
        s.text(x0 - 18, y + 14, "phase cⱼ has period " + str(len(r["word"])), size=10.5,
               anchor="end", fill=t.muted)
        a, b = X(float(r["original"])), X(float(r["translated"]))
        s.line(b + 9, y, a - 9, y, t.ink2, sw=1.5)
        s.path(f"M{b + 9} {y} l7 -4 v8 z", fill=t.ink2)
        s.circle(a, y, 7, t.resonance, stroke=t.surface, sw=2)
        s.circle(b, y, 6, t.surface, stroke=t.resonance, sw=2.5)
        s.text(a, y - 14, str(r["original"]), size=12, anchor="middle", weight="600")
        s.text(b, y - 14, str(r["translated"]), size=12, anchor="middle")
    ly = H - 50
    s.circle(30, ly - 4, 6, t.resonance)
    s.text(42, ly, "D(X), zero-shell density", size=11.5, fill=t.ink2)
    s.circle(230, ly - 4, 5.5, t.surface, stroke=t.resonance, sw=2.5)
    s.text(242, ly, "D(mX + 1/3) = D(X) · 2/3", size=11.5, fill=t.ink2)
    s.footer("Values from Lean theorems binary_three_periods and translated_third_examples (DS-02, DS-03).")
    return s.done()
