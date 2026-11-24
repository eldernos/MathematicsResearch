"""Figure 6: finite-resolution view of the attainable discrepancy spectrum for p = 3.

For b >= 2 and a prime p coprime to b, ``attainable_discrepancy_iff`` identifies the set
S_p of limiting discrepancies of signed Stoneham expansions (over all bounded integer
phase sequences) with the values V_p(s) = (p-1) sum_i s_i / p^(i+1) of binary words s
that are lexicographically at least every suffix. S_p does not depend on b.

Row L of the figure is the finite set P_L of exact discrepancies of all phase sequences
of period at most L, computed with the rational ``cycleMaximum`` of ``periodic_discrepancy``.
Only the zero pattern of the phases matters, so phases in {0, 1} suffice. P_L is a subset
of S_3, and ``cycleMaximum_approximates_historyValue`` puts every point of S_3 within
3^(-L/2) of P_L for even L (a period 2k pattern with error at most 3^(-k)).
"""

from __future__ import annotations

from fractions import Fraction as F

from svg import Svg, fmt, lin_scale

SLUG = "attainable-spectrum"
P = 3
ROWS = [2, 4, 6, 8, 10, 12, 14]
LMAX = ROWS[-1]
EXAMPLES = {"1110": F(27, 40), "10": F(3, 4), "100": F(12, 13)}  # binary_three_periods

META = {
    "number": 6,
    "summary": 'Finite-resolution approximations, by periodic phases, to the set of attainable discrepancies characterized in DS-04.',
    "title": "Finite-resolution visualization of the attainable discrepancy spectrum",
    "caption": (
        "The spectrum *S*₃ is the set of limiting discrepancies *D*∞ of signed Stoneham expansions with "
        "*p* = 3 over all bounded integer phase sequences, for any radix *b* coprime to 3; theorem DS-04 "
        "identifies it with the values Σ 2*s*ᵢ/3ⁱ⁺¹ of the binary words *s*₀*s*₁*s*₂… that are "
        "lexicographically at least each of their suffixes. Row *L* draws a finite subset of *S*₃: the exact "
        "rational discrepancies of all phase sequences of period at most *L*, from the kernel-verified "
        "periodic formula. By the kernel-verified periodic approximation every point of *S*₃ lies within "
        "1/3ᵏ of a tick in row *L* = 2*k*, so the rows converge to *S*₃, but no row is the uncountable set "
        "itself; for example the smallest positive value 2/3 and the value 8/9 are attained only by "
        "nonperiodic phases. Zero, the normal case, is an isolated point of the spectrum. The shaded gap "
        "(3/4, 8/9) is a short deduction from the characterization, not a separate Lean theorem: a dominating "
        "word beginning 10 cannot contain 11, so it is at most 1010…, of value 3/4, while a word beginning 11 "
        "has value at least 8/9."
    ),
    "alt": (
        "Top strip: a horizontal axis from 0 to 1 with a single aqua tick at 0 labelled normal and isolated, "
        "an empty stretch up to 2/3, and dense blue ticks between 2/3 and 1. Connector lines enlarge the "
        "interval from 2/3 to 1 into a lower panel with seven rows of blue rug ticks for period bounds L = 2, "
        "4, 6, 8, 10, 12 and 14, containing 3, 8, 23, 71, 226, 747 and 2538 distinct values. The ticks fill "
        "in a Cantor-like pattern; a shaded band marks the empty gap between 3/4 and 8/9. Triangles mark the "
        "kernel-verified examples 27/40, 3/4 and 12/13."
    ),
    "provenance": "exact",
    "results": ["DS-04"],
    "sources": [
        "NormalityChecker.SignedPhases.attainable_discrepancy_iff",
        "NormalityChecker.SignedPhases.cycleMaximum_approximates_historyValue",
        "NormalityChecker.SignedPhases.least_positive_historyValue",
        "NormalityChecker.SignedPhases.periodic_discrepancy",
        "notes/attainable-shell-histories.md",
    ],
}


def cycle_maximum(c: list[int]) -> F:
    """SignedShellDiscrepancy.cycleMaximum p L c for the phase word c of length L."""
    L = len(c)
    mass = [0]
    for j in range(L):
        mass.append(mass[-1] + (P ** (j + 1) - P ** j if c[j] == 0 else 0))
    A = F(mass[L], P ** L - 1)
    return max([F(0)] + [(mass[r] + A) / P ** r for r in range(L)])


def word_value(u: str) -> F:
    """V_p(u u u ...) for a finite binary word u."""
    L = len(u)
    n = sum(int(ch) * P ** (L - 1 - i) for i, ch in enumerate(u))
    return F((P - 1) * n, P ** L - 1)


def suffix_maximal_periodic(u: str) -> bool:
    """SuffixMaximal for the periodic word u u u ...; comparing 2L digits decides it."""
    w = u * 3
    return all(w[h:h + 2 * len(u)] <= w[:2 * len(u)] for h in range(1, len(u) + 1))


def compute():
    by_period: dict[int, set] = {}
    for L in range(1, LMAX + 1):
        vals = set()
        for k in range(2 ** L):
            z = format(k, f"0{L}b")  # z_j = 1 marks a zero phase
            c = [1 - int(ch) for ch in z]
            d = cycle_maximum(c)
            # The note: the maximum is the largest reversed cyclic rotation read in radix p.
            rz = z[::-1]
            u = max(rz[i:] + rz[:i] for i in range(L))
            if L <= 10:
                assert d == word_value(u), (z, d)
                assert suffix_maximal_periodic(u)  # so d lies in S_3 (attainable_discrepancy_iff)
            vals.add(d)
        by_period[L] = vals
    rows = []
    cumulative: set = set()
    for L in range(1, LMAX + 1):
        cumulative |= by_period[L]
        if L in ROWS:
            rows.append({"L": L, "values": sorted(cumulative), "bound": F(1, P ** (L // 2))})
    last = rows[-1]["values"]
    positive = [v for v in last if v > 0]
    # Checks against the Lean statements.
    for w, v in EXAMPLES.items():  # binary_three_periods
        assert cycle_maximum([int(ch) for ch in w]) == v and v in rows[1]["values"]
    assert all(F(0) in r["values"] and F(1) in r["values"] for r in rows)
    assert min(positive) > F(2, 3)  # least_positive_historyValue: 2/3 attained only by 1000...
    # Single-one periodic words approach 2/3 from above: (p-1)p^(L-1)/(p^L-1).
    assert min(positive) == F((P - 1) * P ** (LMAX - 1), P ** LMAX - 1)
    # Gap (3/4, 8/9): words starting 10 avoid 11, hence are at most (10)^inf; words starting 11 are
    # at least 11000... with value 8/9. Both endpoints lie in S_3; 8/9 is not periodic.
    assert not [v for v in last if F(3, 4) < v <= F(8, 9)]
    counts = [len(r["values"]) for r in rows]
    assert counts == [3, 8, 23, 71, 226, 747, 2538], counts
    least = {}
    for L in range(1, LMAX + 1):
        for v in by_period[L]:
            least.setdefault(v, L)
    return {"rows": rows, "p": P, "least_period": least}


def data_files(data):
    # Row L of the figure consists of the values whose least period is at most L.
    lines = ["discrepancy,decimal,least_period"]
    for v in data["rows"][-1]["values"]:
        lines.append(f"{v},{float(v):.12f},{data['least_period'][v]}")
    return {"attainable-spectrum.csv": "\n".join(lines) + "\n"}


def frac_label(v: F) -> str:
    return str(v)


SUP = str.maketrans("0123456789-", "⁰¹²³⁴⁵⁶⁷⁸⁹⁻")

def rug(s, xs, y, h, colour, w=1.0):
    """Draw 1 px rug ticks as one path, merging ticks that overlap at pixel scale.

    Ticks closer than ``w`` merge into one filled run from the first to the last tick,
    which renders identically to drawing every tick and keeps the SVG small.
    """
    xs = sorted(xs)
    runs = []
    for x in xs:
        if runs and x - runs[-1][1] <= w:
            runs[-1][1] = x
        else:
            runs.append([x, x])
    d = "".join(f"M{fmt(a - w / 2)} {fmt(y)}h{fmt(b - a + w)}v{fmt(h)}h{fmt(-(b - a + w))}z" for a, b in runs)
    s.path(d, fill=colour)



def render(data, t):
    W, H = 720, 584
    s = Svg(W, H, t, META["title"], META["alt"])
    s.heading("The attainable discrepancy spectrum for p = 3",
              "Exact discrepancies of all periodic phase sequences, period at most L")
    s.badge("exact", y=68)
    rows = data["rows"]
    x0, x1 = 92, 560
    # --- overview strip on [0, 1] ------------------------------------------------
    O = lin_scale(0, 1, x0, x1)
    oy = 132
    s.text(x0 - 12, oy + 4, "[0, 1]", size=13, anchor="end", fill=t.ink2)
    s.line(x0, oy + 12, x1, oy + 12, t.rule)
    rug(s, [O(float(v)) for v in rows[-1]["values"] if v > 0], oy - 6, 18, t.exact)
    s.line(O(0), oy - 6, O(0), oy + 12, t.normal, sw=3)
    for v, lab in ((0, "0"), (1 / 3, "1/3"), (2 / 3, "2/3"), (1, "1")):
        s.line(O(v), oy + 12, O(v), oy + 16, t.rule)
        s.text(O(v), oy + 30, lab, size=13, anchor="middle", fill=t.ink2)
    s.text(O(0) - 4, oy - 14, "0: normal, isolated", size=13, fill=t.ink2)
    s.text(O(0.38), oy + 5, "no attainable value in (0, 2/3)", size=13,
           anchor="middle", fill=t.muted)
    s.text(x1 + 10, oy + 4, f"L ≤ {rows[-1]['L']}", size=13, fill=t.ink2)

    # --- zoom panel on [2/3, 1] --------------------------------------------------
    X = lin_scale(2 / 3, 1, x0, x1)
    row_h = 30
    zt = 232  # top of first row
    zb = zt + row_h * len(rows)
    # connectors from overview interval to panel
    s.line(O(2 / 3), oy + 36, x0, zt - 30, t.rule, dash="3 3")
    s.line(O(1), oy + 36, x1, zt - 30, t.rule, dash="3 3")
    # gap band (3/4, 8/9)
    s.rect(X(3 / 4), zt - 6, X(8 / 9) - X(3 / 4), zb - zt + 6, fill=t.panel)
    s.text((X(3 / 4) + X(8 / 9)) / 2, zt + 3 * row_h + 4, "gap: no attainable", size=13,
           anchor="middle", fill=t.ink2)
    s.text((X(3 / 4) + X(8 / 9)) / 2, zt + 3 * row_h + 22, "value in (3/4, 8/9)", size=13,
           anchor="middle", fill=t.ink2)
    # verified examples: markers above the panel and guides through the rows
    for v in sorted(EXAMPLES.values()):
        xv = X(float(v))
        s.line(xv, zt - 8, xv, zb, t.ink2, sw=1, dash="2 3")
        s.path(f"M{xv - 5} {zt - 18} L{xv + 5} {zt - 18} L{xv} {zt - 10} Z", fill=t.ink)
    s.text(X(27 / 40) - 4, zt - 24, "27/40", size=13, anchor="end", weight="600")
    s.text(X(3 / 4) + 4, zt - 24, "3/4", size=13, weight="600")
    s.text(X(12 / 13), zt - 24, "12/13", size=13, anchor="middle", weight="600")
    # column headers
    s.text(628, zt - 24, "values", size=13, anchor="end", fill=t.ink2)
    s.text(698, zt - 24, "error", size=13, anchor="end", fill=t.ink2)
    for i, r in enumerate(rows):
        y = zt + i * row_h
        s.text(x0 - 12, y + 15, f"L ≤ {r['L']}", size=13, anchor="end")
        rug(s, [X(float(v)) for v in r["values"] if v > 0], y + 2, 18, t.exact)
        s.text(628, y + 15, f"{len(r['values'])}", size=13, anchor="end", fill=t.ink2)
        s.text(698, y + 15, f"≤ 3{('-' + str(r['L'] // 2)).translate(SUP)}", size=13, anchor="end",
               fill=t.ink2)
    s.line(x0, zb + 2, x1, zb + 2, t.rule)
    for v, lab in ((2 / 3, "2/3"), (3 / 4, "3/4"), (8 / 9, "8/9"), (1, "1")):
        s.line(X(v), zb + 2, X(v), zb + 7, t.rule)
        s.text(X(v), zb + 22, lab, size=13, anchor="middle", fill=t.ink2)
    s.text((x0 + x1) / 2, zb + 42, "limiting interval discrepancy D∞ (enlarged: 2/3 to 1)", size=13,
           anchor="middle", fill=t.ink2)
    # legend
    ly = zb + 74
    s.line(24, ly - 10, 24, ly + 4, t.exact, sw=2)
    s.text(34, ly + 1, "exact D∞ of a periodic phase sequence", size=13, fill=t.ink2)
    s.line(312, ly - 10, 312, ly + 4, t.normal, sw=3)
    s.text(322, ly + 1, "D∞ = 0, normal", size=13, fill=t.ink2)
    s.path(f"M{450} {ly - 9} L{460} {ly - 9} L{455} {ly - 1} Z", fill=t.ink)
    s.text(468, ly + 1, "kernel-verified example (Fig. 4)", size=13, fill=t.ink2)
    s.text(24, ly + 24, "Error: every point of the full spectrum lies within this distance of a tick in its row.",
           size=13, fill=t.ink2)
    s.footer("Lean: attainable_discrepancy_iff, cycleMaximum_approximates_historyValue (DS-04).")
    return s.done()
