"""Figure 1: the insertion lattice of the binary Stoneham square.

Squaring alpha = sum_{j>=1} 3^-j 2^-(3^j) gives the absolutely convergent double series

    alpha^2 = sum over ordered pairs (i, j), i, j >= 1, of 3^-(i+j) 2^-(3^i + 3^j).

The pair (i, j) inserts its term at binary position 3^i + 3^j with coefficient
3^-(i+j). The figure draws the pairs with 1 <= i, j <= 6 and shades the pairs retained
by the Lean prefix ``NormalityChecker.StonehamSquare.pre`` at one digit position n
(``mem_active``: retained iff 3^i + 3^j <= n).

``compute`` checks, with exact integers and fractions,
  * the shaded set equals the upward-closed set U_t of notes/stoneham-powers-products.md,
    in offset coordinates (k - i, k - j) with t = n / 3^k, restricted to positive indices;
  * it has the shape used in the proof of ``exact_profile`` (old square full, two arms);
  * its top-degree layer has 3 pairs and the next layer 4, the hypotheses of the
    cancellation lemma, and the reduced denominator of ``pre n`` computed directly from
    the definition is 3^(2k - 3), as ``exact_profile`` states on that interval.
"""

from __future__ import annotations

from fractions import Fraction as F
from html import escape
import json

from svg import Svg, fmt, log_scale

SLUG = "stoneham-square-lattice"
SIZE = 6           # pairs 1 <= i, j <= SIZE
N = 270            # representative digit position: 3^5 + 3^3, left end of the cancellation interval
META = {
    "number": 1,
    "summary": 'Squaring the binary Stoneham number creates a two-dimensional lattice of insertions; the pairs kept at one digit position form the upward-closed set used in the proof of ST-01.',
    "title": "Stoneham square insertion lattice showing the pairwise products of terms",
    "caption": (
        "The *j*th term of α = α₂,₃ is inserted at binary position 3ʲ, a sparse one-dimensional "
        "sequence. Squaring turns it into a two-dimensional lattice: the ordered pair (*i*, *j*) "
        "contributes the coefficient 3⁻⁽ⁱ⁺ʲ⁾ at position 3ⁱ + 3ʲ, and (*i*, *j*) and (*j*, *i*) "
        "share a position, so off the diagonal the coefficient there is 2·3⁻⁽ⁱ⁺ʲ⁾. Blue cells are "
        "the pairs kept by the exact shifted prefix at digit *n* = 270 = 3⁵ + 3³, those with "
        "3ⁱ + 3ʲ ≤ *n*; in the offset coordinates (5 − *i*, 5 − *j*) this is the upward-closed set "
        "*U*ₜ of the polynomial theorem (ST-01) with *t* = *n*/3⁵ = 10/9, restricted to positive "
        "indices. Its top layer *i* + *j* = 8 has three pairs, so one factor of 3 cancels and the "
        "reduced denominator is 3⁷ rather than 3⁸, as in the exact profile (ST-03). Positions, the "
        "kept set and the denominator are exact computations checked against the Lean definitions."
    ),
    "alt": (
        "A 6 by 6 grid of cells indexed by i from 1 to 6 left to right and j from 1 to 6 bottom to "
        "top. Each cell shows the insertion position 3 to the i plus 3 to the j and the "
        "coefficient 3 to the minus (i + j); the grid is symmetric about the diagonal. Positions "
        "range from 6 in the corner (1, 1) to 1458 in the corner (6, 6). Twenty-two cells are "
        "shaded blue: all pairs with both indices at most 4, plus (5, 1), (5, 2), (5, 3) and their "
        "transposes, the pairs whose position is at most 270. Cells (4, 4), (5, 3) and (3, 5) on "
        "the anti-diagonal i + j = 8 have an orange outline. Below, a logarithmic number line "
        "from about 2 to 1600 shows the 6 insertion positions 3 to the j of alpha in one row and the "
        "21 distinct positions of alpha squared in a second row, clustered just after each power "
        "of 3, with a vertical marker at n = 270; positions up to 270 are blue."
    ),
    "provenance": "exact",
    "results": ["ST-01", "ST-03"],
    "sources": [
        "NormalityChecker.StonehamSquare.mem_active",
        "NormalityChecker.StonehamSquare.pre",
        "NormalityChecker.StonehamSquare.exact_profile",
        "NormalityChecker.StonehamPolynomial.prime_power_polynomial_normal",
        "notes/stoneham-square.md",
        "notes/stoneham-powers-products.md",
    ],
}


def scale_of(n: int) -> int:
    k = 0
    while 3 ** (k + 1) <= n:
        k += 1
    return k


def pre(n: int) -> F:
    """The Lean prefix: sum over ordered pairs with 3^i + 3^j <= n (indices from one)."""
    total = F(0)
    i = 1
    while 3 ** i < n:
        j = 1
        while 3 ** i + 3 ** j <= n:
            total += F(2 ** (n - 3 ** i - 3 ** j), 3 ** (i + j))
            j += 1
        i += 1
    return total


def compute():
    k = scale_of(N)
    t = F(N, 3 ** k)
    cells = []
    for i in range(1, SIZE + 1):
        for j in range(1, SIZE + 1):
            pos, deg = 3 ** i + 3 ** j, i + j
            active = pos <= N
            # upward-closed set U_t in offsets a = k - i, b = k - j (positive indices only)
            if i <= k and j <= k:
                in_u = F(1, 3 ** (k - i)) + F(1, 3 ** (k - j)) <= t
            else:
                in_u = False
            assert active == in_u, (i, j)
            # exact_profile proof shape: old square full, arms through index k - 2
            shape = (i <= k and j <= k and (i < k or j <= k - 2) and (j < k or i <= k - 2))
            assert active == shape, (i, j)
            cells.append({"i": i, "j": j, "position": pos, "degree": deg, "active": active})
    act = [c for c in cells if c["active"]]
    top = max(c["degree"] for c in act)
    top_layer = [c for c in act if c["degree"] == top]
    next_layer = [c for c in act if c["degree"] == top - 1]
    assert top == 2 * k - 2 and len(top_layer) == 3 and len(next_layer) == 4
    q = pre(N).denominator
    assert q == 3 ** (2 * k - 3), q
    for c in cells:
        c["top_layer"] = c in top_layer
    alpha_pos = [3 ** j for j in range(1, SIZE + 1)]
    mult: dict[int, int] = {}
    for c in cells:
        mult[c["position"]] = mult.get(c["position"], 0) + 1
    return {"n": N, "k": k, "t": t, "cells": cells, "q": q, "top": top,
            "alpha_positions": alpha_pos, "square_positions": sorted(mult.items())}


def data_files(data):
    lines = ["i,j,insertion_position,coefficient,active_at_n,top_active_degree"]
    for c in data["cells"]:
        lines.append(f"{c['i']},{c['j']},{c['position']},3^-{c['degree']},"
                     f"{int(c['active'])},{int(c['top_layer'])}")
    summary = {
        "n": data["n"], "scale_k": data["k"], "t": str(data["t"]),
        "active_rule": "3^i + 3^j <= n (Lean mem_active), indices from 1",
        "top_active_degree": data["top"],
        "reduced_denominator_of_pre_n": data["q"],
        "reduced_denominator_power_of_3": data["top"] - 1,
        "alpha_positions": data["alpha_positions"],
        "square_positions_with_ordered_multiplicity": [[p, m] for p, m in data["square_positions"]],
    }
    return {"stoneham-square-lattice.csv": "\n".join(lines) + "\n",
            "stoneham-square-lattice.json": json.dumps(summary, indent=2) + "\n"}


# -- rendering ---------------------------------------------------------------
def mtext(s: Svg, x, y, runs, size=13, anchor="start", fill=None, weight=None):
    """Text with italic and superscript runs. ``runs``: (text, kind) with kind a subset of
    "i" (italic) and "^" (superscript)."""
    fill = fill or s.t.ink
    out, shift = [], 0.0
    for txt, kind in runs:
        target = -0.36 * size if "^" in kind else 0.0
        attrs = []
        if target != shift:
            attrs.append(f'dy="{fmt(target - shift)}"')
            shift = target
        if "^" in kind:
            attrs.append(f'font-size="{fmt(round(size * 0.74, 1))}"')
        if "i" in kind:
            attrs.append('font-style="italic"')
        out.append(f'<tspan {" ".join(attrs)}>{escape(txt)}</tspan>' if attrs else
                   f"<tspan>{escape(txt)}</tspan>")
    a = f' text-anchor="{anchor}"' if anchor != "start" else ""
    w = f' font-weight="{weight}"' if weight else ""
    s.add(f'<text x="{fmt(x)}" y="{fmt(y)}" font-size="{fmt(size)}" fill="{fill}"{a}{w}>'
          f'{"".join(out)}</text>')


def render(data, t):
    W, H = 720, 680
    s = Svg(W, H, t, META["title"], META["alt"])
    s.heading("Squaring creates a two-dimensional insertion lattice")
    mtext(s, 24, 56, [("Pair (", ""), ("i", "i"), (", ", ""), ("j", "i"), (") inserts 3", ""),
                      ("−(i+j)", "^i"), (" at binary position 3", ""), ("i", "^i"), (" + 3", ""),
                      ("j", "^i"), ("; blue pairs are kept at digit ", ""), ("n", "i"),
                      (" = 270", "")], size=13.5, fill=t.ink2)
    s.badge("exact", y=74)
    act_op = 0.24 if t.name == "light" else 0.36

    cs, gx, gy = 54, 76, 118                # cell size, grid origin (top-left)
    gb = gy + cs * SIZE                      # grid bottom
    cx = lambda i: gx + (i - 1) * cs
    cy = lambda j: gb - j * cs
    for c in data["cells"]:
        x, y = cx(c["i"]), cy(c["j"])
        if c["active"]:
            s.rect(x + 1, y + 1, cs - 2, cs - 2, fill=t.exact, opacity=act_op, rx=4)
        else:
            s.rect(x + 1, y + 1, cs - 2, cs - 2, fill=t.panel, stroke=t.grid, rx=4)
        s.text(x + cs / 2, y + 23, str(c["position"]), size=14, anchor="middle",
               weight="600" if c["active"] else None, fill=t.ink if c["active"] else t.ink2)
        mtext(s, x + cs / 2, y + 42, [("3", ""), (f"−{c['degree']}", "^")], size=13,
              anchor="middle", fill=t.ink2)
    for c in data["cells"]:
        if c["top_layer"]:
            s.rect(cx(c["i"]) + 1.5, cy(c["j"]) + 1.5, cs - 3, cs - 3, stroke=t.resonance, sw=3, rx=4)
    for v in range(1, SIZE + 1):
        s.text(cx(v) + cs / 2, gb + 19, str(v), size=13, anchor="middle", fill=t.ink2)
        s.text(gx - 10, cy(v) + cs / 2 + 4.5, str(v), size=13, anchor="end", fill=t.ink2)
    mtext(s, gx + cs * SIZE / 2, gb + 39, [("index ", ""), ("i", "i")], anchor="middle", fill=t.ink2)
    mtext(s, gx - 32, gy + cs * SIZE / 2, [("j", "i")], anchor="middle", fill=t.ink2)

    # explanatory legend on the right
    lx, ly = gx + cs * SIZE + 34, gy + 8
    s.rect(lx, ly, 16, 16, fill=t.exact, opacity=act_op, rx=3)
    mtext(s, lx + 26, ly + 13, [("kept at ", ""), ("n", "i"), (" = 270: 3", ""), ("i", "^i"),
                                (" + 3", ""), ("j", "^i"), (" ≤ ", ""), ("n", "i")], fill=t.ink2)
    s.rect(lx, ly + 28, 16, 16, fill=t.panel, stroke=t.grid, rx=3)
    s.text(lx + 26, ly + 41, "inserted only after digit 270", size=13, fill=t.ink2)
    s.rect(lx + 1, ly + 57, 14, 14, stroke=t.resonance, sw=3, rx=3)
    mtext(s, lx + 26, ly + 69, [("top kept degree ", ""), ("i", "i"), (" + ", ""), ("j", "i"),
                                (" = 8: three pairs,", "")], fill=t.ink2)
    mtext(s, lx + 26, ly + 87, [("hence ", ""), ("q", "i"), ("₂₇₀", ""), (" = 3", ""),
                                ("7", "^"), (", not 3", ""), ("8", "^")], fill=t.ink2)
    notes = [
        [("Upper number: insertion position 3", ""), ("i", "^i"), (" + 3", ""), ("j", "^i")],
        [("Lower: coefficient 3", ""), ("−(i+j)", "^i"), (" of the pair", "")],
        [("Pairs (", ""), ("i", "i"), (", ", ""), ("j", "i"), (") and (", ""), ("j", "i"), (", ", ""),
         ("i", "i"), (") share a position:", "")],
        [("off the diagonal the coefficient is 2·3", ""), ("−(i+j)", "^i")],
        [("Shell 3", ""), ("5", "^"), (" = 243 ≤ ", ""), ("n", "i"), (" < 3", ""), ("6", "^"),
         (", ", ""), ("t", "i"), (" = ", ""), ("n", "i"), ("/3", ""), ("5", "^"), (" = 10/9", "")],
        [("In offsets (5 − ", ""), ("i", "i"), (", 5 − ", ""), ("j", "i"),
         (") the blue set is ", ""), ("U", "i"), ("ₜ", "")],
    ]
    for y, run in zip((ly + 132, ly + 153, ly + 184, ly + 205, ly + 236, ly + 257), notes):
        mtext(s, lx, y, run, fill=t.ink2)

    # number line of insertion positions
    top = gb + 76
    mtext(s, 24, top, [("Insertion positions on a logarithmic axis", "")], size=14, weight="600")
    x0, x1 = 120, W - 150
    X = log_scale(2.5, 1600, x0, x1)
    nsq = len(data["square_positions"])
    rows = [("α: 3", "j", data["alpha_positions"], top + 38, f"{len(data['alpha_positions'])} positions"),
            ("α²: 3", "i", [p for p, _ in data["square_positions"]], top + 80, f"{nsq} positions")]
    for k in range(1, 7):
        s.line(X(3 ** k), top + 18, X(3 ** k), top + 96, t.grid)
        mtext(s, X(3 ** k), top + 116, [("3", ""), (str(k), "^")], anchor="middle", fill=t.ink2)
    for label, var, ps, y, count in rows:
        s.line(x0, y, x1, y, t.rule)
        if var == "j":
            mtext(s, x0 - 14, y + 4.5, [(label, ""), ("j", "^i")], anchor="end", fill=t.ink2)
        else:
            mtext(s, x0 - 14, y + 4.5, [(label, ""), ("i", "^i"), (" + 3", ""), ("j", "^i")],
                  anchor="end", fill=t.ink2)
        for p in ps:
            on = p <= data["n"]
            s.line(X(p), y - 11, X(p), y + 11, t.exact if on else t.muted, sw=2.4 if on else 1.6)
        s.text(x1 + 16, y + 4.5, count, size=13, fill=t.ink2)
    mtext(s, x1 + 16, top + 102, [("indices ≤ 6", "")], fill=t.muted)
    s.line(X(data["n"]), top + 16, X(data["n"]), top + 98, t.ink, sw=1.5, dash="4 3")
    mtext(s, X(data["n"]) - 6, top + 16, [("n", "i"), (" = 270", "")], size=13, anchor="end")
    s.footer("Active set as in Lean mem_active (3ⁱ + 3ʲ ≤ n); denominator as in exact_profile "
             "(ST-01, ST-03).")
    return s.done()
