"""Figure 4: uniform and resonant shells of three binary signed Stoneham expansions.

For bounded integer phases c_j, put a_0 = c_0, a_{j+1} = c_{j+1} - p c_j and
X = sum_j a_j / (p^j b^{p^j}). Shell j holds the positions p^j <= n < p^{j+1}; it is a
zero shell when c_j = 0. Z(N) counts zero-shell positions among 0 <= n < N (position 0
precedes all shells). DS-01 (``discrepancy_sub_zeroDensity_tendsto``) states
D_N - Z(N)/N -> 0, so the limiting discrepancy is limsup Z(N)/N.

``compute`` counts Z(N) with integers, cross-checks it against the Lean recurrence
for ``boundaryMass``, and recomputes the three limsups of ``binary_three_periods``
with the rational cycle scores of ``cycleMaximum``.
"""

from __future__ import annotations

from fractions import Fraction as F
import math

from svg import Svg, log_scale, lin_scale

SLUG = "signed-shell-regions"
META = {
    "number": 4,
    "summary": 'The exact zero-shell fraction *Z*(*N*)/*N*, which DS-01 identifies with the discrepancy, for three periodic phase words.',
    "title": "Signed-shell uniform and resonant regions",
    "caption": (
        "Binary signed Stoneham expansions with *p* = 3 and repeating phase words 1110, 10 and 100; shell *j* "
        "holds the starting positions 3ʲ ≤ *n* < 3ʲ⁺¹. Asymptotically, the orbit of 2ⁿ*X* modulo 1 is "
        "uniformly distributed on shells with nonzero phase (aqua) and concentrates near 0 modulo 1 on "
        "zero-phase shells (orange). The solid curve is the exact zero-shell fraction *Z*(*N*)/*N*, counted "
        "with integers at every drawn cutoff *N* ≤ 3¹⁰: by theorem DS-01, *D*ₙ − *Z*(*N*)/*N* → 0, so it is the "
        "discrepancy the theorem predicts, not a measurement of *D*ₙ. The dashed lines mark its limsup, the "
        "kernel-verified limiting discrepancies 27/40, 3/4 and 12/13 (DS-02)."
    ),
    "alt": (
        "Three stacked panels, one per phase word 1110, 10 and 100, sharing a logarithmic horizontal axis "
        "of prefix length N from 1 to 3 to the 10th. Above each panel a band of ten equal-width shells is "
        "coloured aqua for nonzero phase and orange for zero phase: every fourth shell for 1110, every "
        "second shell for 10, and two of every three shells for 100. Below, a solid curve shows the exact "
        "fraction Z(N)/N of zero-shell positions, rising across orange shells and falling across aqua ones. "
        "Its peaks approach dashed lines at 27/40, 3/4 and 12/13 respectively."
    ),
    "provenance": "theorem",
    "results": ["DS-01", "DS-02"],
    "sources": [
        "NormalityChecker.SignedPhases.discrepancy_sub_zeroDensity_tendsto",
        "NormalityChecker.SignedPhases.binary_three_periods",
        "NormalityChecker.SignedPhases.periodic_discrepancy",
        "notes/signed-shell-discrepancy.md",
    ],
}

P = 3
J = 10  # shells 0 .. J-1, prefixes up to p^J
WORDS = ["1110", "10", "100"]
LEAN = {"1110": F(27, 40), "10": F(3, 4), "100": F(12, 13)}  # binary_three_periods
SAMPLES_PER_SHELL = 24


def phase(word: str, j: int) -> int:
    return int(word[j % len(word)])


def shell_of(n: int) -> int:
    """Nat.log p n for n >= 1."""
    j = 0
    while P ** (j + 1) <= n:
        j += 1
    return j


def zero_counts(word: str, n_max: int) -> list[int]:
    """Z(N) for 0 <= N <= n_max, by direct counting as in SignedShellDiscrepancy.mass."""
    z = [0] * (n_max + 1)
    for n in range(n_max):
        zero = n != 0 and phase(word, shell_of(n)) == 0
        z[n + 1] = z[n] + (1 if zero else 0)
    return z


def boundary_mass(word: str, j: int) -> int:
    """SignedShellDiscrepancy.boundaryMass."""
    m = 0
    for i in range(j):
        if phase(word, i) == 0:
            m += P ** (i + 1) - P ** i
    return m


def cycle_maximum(word: str) -> F:
    """SignedShellDiscrepancy.cycleMaximum for the word repeated with period L."""
    L = len(word)
    A = F(boundary_mass(word, L), P ** L - 1)
    return max([F(0)] + [(boundary_mass(word, r) + A) / P ** r for r in range(L)])


def sample_points() -> list[int]:
    pts = {1, 2}
    for j in range(J):
        lo, hi = P ** j, P ** (j + 1)
        pts.update((lo, hi))
        for k in range(1, SAMPLES_PER_SHELL):
            pts.add(round(lo * (hi / lo) ** (k / SAMPLES_PER_SHELL)))
    return sorted(p for p in pts if 1 <= p <= P ** J)


def compute():
    n_max = P ** J
    grid = sample_points()
    panels = []
    for w in WORDS:
        z = zero_counts(w, n_max)
        lim = cycle_maximum(w)
        assert lim == LEAN[w], (w, lim)
        L = len(w)
        A = F(boundary_mass(w, L), P ** L - 1)
        for j in range(J + 1):
            assert z[P ** j] == boundary_mass(w, j)
            # Lean identity in periodic_discrepancy: Z(p^j)/p^j = cycleScore(j mod L) - A/p^j
            r = j % L
            assert F(z[P ** j], P ** j) == (boundary_mass(w, r) + A) / P ** r - A / P ** j
        # Within a shell the fraction is monotone, so the boundary values bound every cutoff.
        for j in range(J):
            lo, hi = P ** j, P ** (j + 1)
            ends = (F(z[lo], lo), F(z[hi], hi))
            inner = [F(z[n], n) for n in range(lo, hi + 1)]
            assert max(inner) == max(ends) and min(inner) == min(ends)
        curve = [(N, F(z[N], N)) for N in grid]
        assert all(v < lim for _, v in curve)  # boundary densities approach the limsup from below
        panels.append({
            "word": w, "limsup": lim,
            "zero_shells": [j for j in range(J) if phase(w, j) == 0],
            "curve": curve,
            "peak": max(curve, key=lambda nv: nv[1]),
        })
    return {"panels": panels, "p": P, "shells": J}


def data_files(data):
    lines = ["phase_word,N,Z_N,Z_over_N"]
    for pan in data["panels"]:
        for N, v in pan["curve"]:
            lines.append(f"{pan['word']},{N},{v * N},{v}")
    return {"signed-shell-regions.csv": "\n".join(lines) + "\n"}


def render(data, t):
    W = 720
    panels = data["panels"]
    band_h, plot_h, gap, title_h = 14, 92, 40, 26
    top = 124
    H = top + len(panels) * (title_h + band_h + 6 + plot_h + gap) + 40
    s = Svg(W, H, t, META["title"], META["alt"])
    s.heading("Zero-phase shells carry the whole discrepancy",
              "Binary signed expansions with p = 3: exact zero-shell fraction Z(N)/N")
    s.badge("theorem", y=68)
    # legend
    ly = 108
    s.swatch(24, ly, "normal", "nonzero phase: orbit uniform mod 1")
    s.swatch(282, ly, "resonance", "zero phase: orbit near 0 mod 1")
    s.line(522, ly - 3, 546, ly - 3, t.ink, sw=2)
    s.text(552, ly + 1, "Z(N)/N", size=13, fill=t.ink2)
    s.line(612, ly - 3, 636, ly - 3, t.ink2, sw=1.5, dash="5 4")
    s.text(642, ly + 1, "limsup", size=13, fill=t.ink2)

    x0, x1 = 60, W - 84
    X = log_scale(1, P ** data["shells"], x0, x1)
    y = top
    for k, pan in enumerate(panels):
        # panel title and shell band
        s.text(x0, y + 16, f"phase word {pan['word']}", size=14, weight="600")
        digits = " ".join(f"c{str(i).translate(SUB)}" for i in range(len(pan["word"])))
        s.text(x0 + 128, y + 16, f"phases {digits} = {' '.join(pan['word'])}, repeated", size=13,
               fill=t.ink2)
        by = y + title_h
        for j in range(data["shells"]):
            a, b = X(P ** j), X(P ** (j + 1))
            kind = t.resonance if j in pan["zero_shells"] else t.normal
            s.rect(a + 1, by, b - a - 2, band_h, fill=kind, rx=2)
        # plot
        py0 = by + band_h + 6
        py1 = py0 + plot_h
        Y = lin_scale(0, 1, py1, py0)
        for v in (0, 0.5, 1):
            s.line(x0, Y(v), x1, Y(v), t.grid)
            s.text(x0 - 8, Y(v) + 4.5, f"{v:g}", size=13, anchor="end", fill=t.muted)
        for j in range(data["shells"] + 1):
            s.line(X(P ** j), py0, X(P ** j), py1, t.grid)
        lim = float(pan["limsup"])
        s.line(x0, Y(lim), x1, Y(lim), t.ink2, sw=1.5, dash="5 4")
        s.text(x1 + 8, Y(lim) + 4.5, str(pan["limsup"]), size=14, weight="600")
        s.polyline([(X(N), Y(float(v))) for N, v in pan["curve"]], t.ink, sw=2)
        if k == len(panels) - 1:
            for j in range(data["shells"] + 1):
                s.text(X(P ** j), py1 + 18, f"3{str(j).translate(SUP)}", size=13, anchor="middle",
                       fill=t.ink2)
            s.text((x0 + x1) / 2, py1 + 40, "prefix length N (logarithmic; ticks at shell boundaries)",
                   size=13, anchor="middle", fill=t.ink2)
        y = py1 + gap
    s.footer("Lean: discrepancy_sub_zeroDensity_tendsto and binary_three_periods (DS-01, DS-02).")
    return s.done()


SUP = str.maketrans("0123456789", "⁰¹²³⁴⁵⁶⁷⁸⁹")
SUB = str.maketrans("0123456789", "₀₁₂₃₄₅₆₇₈₉")
