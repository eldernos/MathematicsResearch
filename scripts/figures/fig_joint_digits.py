"""Figure 8: finite-sample joint digit frequencies of alpha, alpha^2 and alpha^3,
alpha = sum_{j>=1} 3^-j 2^-(3^j) (the binary Stoneham number alpha_{2,3}).

For r = 1, 2, 3 and 0 <= n < N the first four binary digits of x_n^(r) = {2^n alpha^r}
are floor(16 x_n^(r)) = floor(2^(n+4) alpha^r) mod 16, read off the single integer
floor(2^M alpha^r) with M = N + 64.

Exactness. alpha is truncated after the term j = J, where J is the least index with
3^(J+1) > M + 64. The omitted tail is positive and below 3^-J 2^-(3^(J+1)) / 2, so
alpha lies in [lo, hi] with exact rationals lo, hi. ``compute`` asserts that
floor(2^M lo^r) = floor(2^M hi^r) for each r, hence these integers equal
floor(2^M alpha^r) exactly: there is no last-bit (plus or minus one) uncertainty in any
digit used. All counts are exact; the chi-square statistics are exact rationals,
rounded only for display.

This is a numerical illustration. No finite sample bears on the limit; the limit
statement is the Lean theorem
``NormalityChecker.StonehamPolynomial.joint_uniform_powers`` (ST-05).
"""

from __future__ import annotations

from fractions import Fraction as F
import json

from svg import Svg

SLUG = "stoneham-joint-digits"
N = 16384          # orbit length
BITS = 4           # 16 bins per coordinate
GUARD = 64
PAIRS = ((1, 2), (1, 3), (2, 3))
# Values quoted in the caption and alt text; compute() asserts them.
QUOTED = {(1, 2): ("253.7", "0.69", "1.44"), (1, 3): ("235.2", "0.73", "1.47"),
          (2, 3): ("243.3", "0.69", "1.33")}
CLASSES = (F(4, 5), F(9, 10), F(11, 10), F(6, 5))      # class boundaries for count / expected

META = {
    "number": 8,
    "summary": 'Numerical illustration only: joint digit histograms of α, α² and α³ over 16 384 positions. The limit statement is the theorem ST-05.',
    "title": "Illustrative joint distributions of digits of distinct Stoneham powers",
    "caption": (
        "Each panel is a 16 × 16 histogram of the first four binary digits of two powers of "
        "α = α₂,₃ along the same orbit: the cell (*a*, *b*) counts the *n* < 16 384 with "
        "⌊16{2ⁿαʳ}⌋ = *a* and ⌊16{2ⁿαˢ}⌋ = *b*, for (*r*, *s*) = (1, 2), (1, 3) and (2, 3). "
        "Shading gives the count divided by the uniform expectation 64; the observed ratios lie "
        "between 0.69 and 1.47, and the chi-square statistics on 255 degrees of freedom are "
        "253.7, 235.2 and 243.3. The digits are exact, since α is truncated with a certified tail "
        "bound and no digit is affected by rounding, but the figure is a numerical illustration: "
        "a finite sample is not evidence about the limit. The limit statement, that for distinct "
        "positive exponents the vectors of fractional parts {2ⁿαʳ} are jointly uniformly "
        "distributed in the unit cube, is the Lean theorem ST-05."
    ),
    "alt": (
        "Three square heat maps side by side, titled alpha against alpha squared, alpha against "
        "alpha cubed, and alpha squared against alpha cubed. Each is a 16 by 16 grid over the unit "
        "square, horizontal axis the fractional part of 2 to the n times the first power and "
        "vertical axis that of the second. Cell darkness in a single aqua hue gives the count "
        "divided by the uniform expectation 64, in five classes from below 0.8 to 1.2 or more. "
        "The shading shows no visible structure: most cells fall between 0.9 and 1.1. Below the "
        "panels: chi-square 253.7, 235.2 and 243.3 on 255 degrees of freedom, and count ratios "
        "from 0.69 to 1.44, 0.73 to 1.47, and 0.69 to 1.33. A note states that an independent "
        "uniform sample would give chi-square about 255 plus or minus 23 and that finite counts "
        "are not evidence about the limit."
    ),
    "provenance": "illustration",
    "results": ["ST-05"],
    "sources": [
        "NormalityChecker.StonehamPolynomial.joint_uniform_powers",
        "NormalityChecker/StonehamJoint.lean",
        "notes/stoneham-powers-products.md",
    ],
}


def floors(M: int):
    """Exact floor(2^M alpha^r) for r = 1, 2, 3, certified by a tail enclosure."""
    J = 1
    while 3 ** (J + 1) <= M + GUARD:
        J += 1
    lo = sum((F(1, 3 ** j * 2 ** (3 ** j)) for j in range(1, J + 1)), F(0))
    hi = lo + F(1, 2 * 3 ** J * 2 ** (3 ** (J + 1)))
    out = {}
    for r in (1, 2, 3):
        a, b = lo ** r, hi ** r
        fa = (a.numerator << M) // a.denominator
        fb = (b.numerator << M) // b.denominator
        assert fa == fb, r                       # certified: no last-bit ambiguity
        assert fa >> M == 0                      # alpha^r < 1
        out[r] = fa
    return J, out


def chi_square(counts, expected):
    return sum((F(c) - expected) ** 2 for c in counts) / expected


def compute():
    M = N + GUARD
    J, B = floors(M)
    mask = (1 << BITS) - 1
    bins = {r: [(B[r] >> (M - n - BITS)) & mask for n in range(N)] for r in B}
    E = F(N, 1 << (2 * BITS))
    panels = []
    for r, s in PAIRS:
        grid = [[0] * 16 for _ in range(16)]
        for a, b in zip(bins[r], bins[s]):
            grid[a][b] += 1
        flat = [grid[a][b] for a in range(16) for b in range(16)]
        assert sum(flat) == N
        panels.append({"r": r, "s": s, "grid": grid, "chi2": chi_square(flat, E),
                       "min_ratio": F(min(flat)) / E, "max_ratio": F(max(flat)) / E})
    for p in panels:
        got = (f"{float(p['chi2']):.1f}", f"{float(p['min_ratio']):.2f}", f"{float(p['max_ratio']):.2f}")
        assert got == QUOTED[p["r"], p["s"]], (p["r"], p["s"], got)
    return {"N": N, "M": M, "J": J, "expected": E, "panels": panels}


def data_files(data):
    lines = ["power_x,power_y,bin_x,bin_y,count,count_over_expected"]
    for p in data["panels"]:
        for a in range(16):
            for b in range(16):
                c = p["grid"][a][b]
                lines.append(f"{p['r']},{p['s']},{a},{b},{c},{F(c) / data['expected']}")
    summary = {
        "orbit_length_N": data["N"],
        "bits_per_coordinate": BITS,
        "precision_bits_M": data["M"],
        "alpha_truncated_after_j": data["J"],
        "certification": "floor(2^M lo^r) == floor(2^M hi^r) for r = 1, 2, 3; digits exact",
        "expected_per_cell": str(data["expected"]),
        "degrees_of_freedom": 255,
        "panels": [{
            "powers": [p["r"], p["s"]],
            "chi_square": str(p["chi2"]),
            "chi_square_decimal": round(float(p["chi2"]), 2),
            "min_count_over_expected": str(p["min_ratio"]),
            "max_count_over_expected": str(p["max_ratio"]),
        } for p in data["panels"]],
        "note": "Numerical illustration only; the limit is the Lean theorem joint_uniform_powers (ST-05).",
    }
    return {"stoneham-joint-digits.csv": "\n".join(lines) + "\n",
            "stoneham-joint-digits.json": json.dumps(summary, indent=2) + "\n"}


# -- rendering ---------------------------------------------------------------
SUPR = {1: "", 2: "²", 3: "³"}
OPACITY = (0.10, 0.28, 0.48, 0.70, 0.95)


def level(ratio: F) -> int:
    return sum(1 for c in CLASSES if ratio >= c)


def render(data, t):
    W, H = 720, 492
    s = Svg(W, H, t, META["title"], META["alt"])
    s.heading("Joint digit frequencies of α, α² and α³ (finite sample)",
              f"First 4 binary digits of {{2ⁿαʳ}} for 0 ≤ n < {data['N']:,}".replace(",", " ")
              + "; count per cell divided by the uniform 64")
    s.badge("illustration", y=78)
    cell = 11
    size = cell * 16
    gy = 140
    for idx, p in enumerate(data["panels"]):
        gx = 54 + idx * 232
        r, q = p["r"], p["s"]
        s.text(gx + size / 2, gy - 12, f"α{SUPR[r]} against α{SUPR[q]}", size=14, anchor="middle",
               weight="600")
        for a in range(16):
            for b in range(16):
                ratio = F(p["grid"][a][b]) / data["expected"]
                s.rect(gx + a * cell + 0.5, gy + (15 - b) * cell + 0.5, cell - 1, cell - 1,
                       fill=t.normal, opacity=OPACITY[level(ratio)])
        s.rect(gx, gy, size, size, stroke=t.rule)
        s.text(gx, gy + size + 17, "0", size=13, anchor="middle", fill=t.ink2)
        s.text(gx + size, gy + size + 17, "1", size=13, anchor="middle", fill=t.ink2)
        s.text(gx + size / 2, gy + size + 17, f"{{2ⁿα{SUPR[r]}}}", size=13, anchor="middle",
               fill=t.ink2)
        s.text(gx - 7, gy + size + 4, "0", size=13, anchor="end", fill=t.ink2)
        s.text(gx - 7, gy + 10, "1", size=13, anchor="end", fill=t.ink2)
        s.text(gx - 12, gy + size / 2, f"{{2ⁿα{SUPR[q]}}}", size=13, anchor="middle", fill=t.ink2,
               rotate=-90)
        s.text(gx + size / 2, gy + size + 42, f"χ² = {float(p['chi2']):.1f} on 255 df", size=13,
               anchor="middle")
        s.text(gx + size / 2, gy + size + 60,
               f"ratio {float(p['min_ratio']):.2f} to {float(p['max_ratio']):.2f}", size=13,
               anchor="middle", fill=t.ink2)
    # legend for the sequential classes
    ly = gy + size + 96
    s.text(24, ly, "count / 64", size=13, fill=t.ink2)
    labels = ["below 0.8", "0.8 to 0.9", "0.9 to 1.1", "1.1 to 1.2", "1.2 or more"]
    x = 104
    for op, lab in zip(OPACITY, labels):
        s.rect(x, ly - 11, 14, 14, fill=t.normal, opacity=op, rx=2)
        s.text(x + 20, ly + 1, lab, size=13, fill=t.ink2)
        x += 20 + 7.2 * len(lab) + 22
    s.text(24, ly + 30, "An independent uniform sample would give χ² ≈ 255 ± 23. "
           "Finite counts are not evidence about the limit.", size=13)
    s.footer("Limit statement: Lean joint_uniform_powers (ST-05). Digits exact via a certified "
             "tail bound for α.")
    return s.done()
