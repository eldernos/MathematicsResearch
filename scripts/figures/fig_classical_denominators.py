"""Figure 9: logarithmic growth of the reduced denominators of shifted binary prefixes
for classical constants, against the polynomial regime of the rational-prefix
certificate.

Every curve is an exact computation with ``fractions.Fraction``. Each prefix is the
Lean definition, built by its own recurrence and cross-checked against the defining
sum for small N:

* ``logDen n = (logPrefix n).den`` with ``logPrefix (n+1) = 2 logPrefix n + 1/(n+1)``
  (NormalityChecker/LogTwo.lean, PrimeCancellation.lean); rate 1 by
  ``tendsto_logDen_div`` (DenominatorGrowth.lean).
* ``(twoStridePrefix N).den`` with ``twoStridePrefix = stridedPrefix 2 N (fun _ => 2)
  + stridedPrefix 3 N (fun j => -(-1)^j)`` (StridedLogarithm.lean); the recurrence
  ``StrideDenominatorRate.step`` has weight 4[2|j] + 3[3|j] - 6[6|j]; rate 1/2 by
  ``StrideDenominatorRate.log_denominator_rate``.
* ``(dyadicLogPrefix k N).den`` with ``dyadicLogPrefix k N = 2^(N % k) *
  Polylog.shifted (2^k) 1 (N / k)`` (DyadicLogRates.lean); rate 1/k by
  ``dyadicLogPrefix_rate``.
* the Gaussian arctangent prefix Y_N = 2^N (b_2(M_2) + b_3(M_3)) of
  notes/gaussian-arctangent-denominators.md for arctan(1/2); its rate 2/3 is a paper
  deduction with no Lean theorem.

Logarithms are natural, as in the Lean statements. The violet region is the bound
log q <= d log N that the certificate ``normal_of_arithmetic_certificate`` imposes on a
block-start denominator (den <= (B^k)^d with block length B^k <= n), drawn for d = 3.
"""

from __future__ import annotations

from fractions import Fraction as F
import math

from svg import Svg, fmt, log_scale, lin_scale

SLUG = "classical-denominator-growth"
NMAX = 4096
NMIN = 32  # first plotted position
D_CERT = 3  # polynomial exponent used for the drawn certificate region

META = {
    "number": 9,
    "summary": 'Shifted denominators of classical series grow exponentially, outside the polynomial range the certificates require. This says nothing about the normality of ln 2.',
    "title": "Comparison of logarithmic denominator growth in classical-constant models",
    "caption": (
        "Each curve plots (log *q*(*N*))/*N*, with the natural logarithm, where *q*(*N*) is the "
        "exact reduced denominator of the shifted binary prefix at position *N*, computed with "
        "rational arithmetic up to *N* = 4096 from the Lean definitions and checked against "
        "logDen 10 = 63, the divisibility bounds and the prime-survival bands. The curves are the "
        "standard series for ln 2 (rate 1, CC-03), the half-rate series "
        "2Σ 1/(*j*·4ʲ) + Σ (−1)ʲ⁺¹/(*j*·8ʲ) for ln 2 (rate 1/2, CC-01), the dyadic logarithms "
        "ln(4/3) and ln(8/7) (rates 1/2 and 1/3, CC-06), and a Gaussian model for "
        "arctan(1/2) whose rate 2/3 is a paper deduction only (CC-12). The violet region is the range "
        "log *q* ≤ *d* log *N*, drawn for *d* = 3, that the rational-prefix certificate (AC-01) "
        "allows, in addition to prime factors from a fixed finite set. Exponential growth and "
        "unbounded prime support place these classical models outside the certificate's "
        "hypotheses; this says nothing about whether ln 2 is normal, and the discrepancy bound "
        "0.9999 for ln 2 remains open."
    ),
    "alt": (
        "Line chart. Horizontal axis: position N on a logarithmic scale from 32 to 4096. Vertical "
        "axis: log of the reduced denominator divided by N, from 0 to 1.1. Thin dotted reference "
        "lines mark the theorem rates 1, 2/3, 1/2 and 1/3. A solid grey curve for the standard "
        "ln 2 series fluctuates between about 0.8 and 1 and settles near 0.99, near rate 1. A dash-dot curve for "
        "arctan(1/2), marked paper-only, settles near 2/3. A dashed curve for the half-rate ln 2 "
        "series and open circles for ln(4/3) nearly coincide and approach 1/2. A dotted curve for "
        "ln(8/7) approaches 1/3. A violet shaded region along the bottom, bounded by 3 log N / N, "
        "shrinks toward zero and marks the denominators allowed by the rational-prefix certificate."
    ),
    "provenance": "exact",
    "results": ["CC-01", "CC-03", "CC-06", "CC-12", "AC-01"],
    "sources": [
        "NormalityChecker.logPrefix",
        "NormalityChecker.logDen",
        "NormalityChecker.logDen_ten",
        "NormalityChecker.tendsto_logDen_div",
        "NormalityChecker.twoStridePrefix",
        "NormalityChecker.twoStridePrefix_den",
        "NormalityChecker.twoStridePrefix_survival",
        "NormalityChecker.StrideDenominatorRate.log_denominator_rate",
        "NormalityChecker.dyadicLogPrefix",
        "NormalityChecker.dyadicLogPrefix_rate",
        "NormalityChecker.normal_of_arithmetic_certificate",
        "notes/strided-logarithm.md",
        "notes/gaussian-arctangent-denominators.md",
        "notes/arithmetic-certificates.md",
    ],
}


# -- exact arithmetic -----------------------------------------------------------------

def lcm_upto(n: int) -> int:
    out = 1
    for j in range(2, n + 1):
        out = out * j // math.gcd(out, j)
    return out


def primes_upto(n: int) -> list[int]:
    sieve = bytearray([1]) * (n + 1)
    sieve[:2] = b"\x00\x00"
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
    return [i for i in range(n + 1) if sieve[i]]


def ln_int(q: int) -> float:
    """Natural logarithm of a positive integer of any size."""
    b = q.bit_length()
    if b < 1000:
        return math.log(q)
    s = b - 64
    return math.log(q >> s) + s * math.log(2)


def log_prefix(nmax: int) -> list[F]:
    """logPrefix 0 = 0, logPrefix (n+1) = 2 logPrefix n + 1/(n+1)."""
    y, out = F(0), [F(0)]
    for n in range(1, nmax + 1):
        y = 2 * y + F(1, n)
        out.append(y)
    return out


def stride_weight(j: int) -> int:
    """StrideDenominatorRate.weight."""
    return (4 if j % 2 == 0 else 0) + (3 if j % 3 == 0 else 0) - (6 if j % 6 == 0 else 0)


def two_stride_prefix(nmax: int) -> list[F]:
    """twoStridePrefix via StrideDenominatorRate.step."""
    y, out = F(0), [F(0)]
    for n in range(1, nmax + 1):
        y = 2 * y + F(stride_weight(n), n)
        out.append(y)
    return out


def strided_prefix_def(k: int, n: int, w) -> F:
    """stridedPrefix k N w = sum_{i < N/k} w(i+1) 2^(N - k(i+1)) / (i+1)."""
    return sum((F(w(i + 1) * 2 ** (n - k * (i + 1)), i + 1) for i in range(n // k)), F(0))


def polylog_shifted(base: int, mmax: int) -> list[F]:
    """Polylog.shifted base 1: s 0 = 0, s (m+1) = base * s m + 1/(m+1)."""
    y, out = F(0), [F(0)]
    for m in range(1, mmax + 1):
        y = base * y + F(1, m)
        out.append(y)
    return out


def dyadic_log_prefix(k: int, nmax: int) -> list[F]:
    """dyadicLogPrefix k N = 2^(N % k) * Polylog.shifted (2^k) 1 (N / k)."""
    sh = polylog_shifted(2 ** k, nmax // k)
    return [2 ** (n % k) * sh[n // k] for n in range(nmax + 1)]


def gauss_weight(j: int) -> int:
    """w(j) = -Im((1 - i)^j) / 2^floor(j/2), computed in the Gaussian integers."""
    re, im = 1, 0
    for _ in range(j):
        re, im = re + im, im - re  # multiply by (1 - i)
    assert (-im) % (2 ** (j // 2)) == 0
    return -im // 2 ** (j // 2)


def gauss_exponent(t: int, j: int) -> int:
    """e_t(j) = ceil((2t - 1) j / 2)."""
    return -((-(2 * t - 1) * j) // 2)


def gauss_prefix(nmax: int) -> tuple[list[F], list[tuple[int, int]]]:
    """Y_N = 2^N (b_2(M_2) + b_3(M_3)) for arctan(1/2) = arctan(1/3) + arctan(1/7).

    The retained terms are those with e_t(j) <= N, equivalently j <= M_t = floor(2N/(2t-1)),
    so Y_{N+1} = 2 Y_N + (terms with e_t(j) = N + 1)."""
    new: dict[int, F] = {}
    for t in (2, 3):
        j = 1
        while gauss_exponent(t, j) <= nmax:
            e = gauss_exponent(t, j)
            new[e] = new.get(e, F(0)) + F(gauss_weight(j), j)
            j += 1
    y, out, cut = F(0), [F(0)], [(0, 0)]
    for n in range(1, nmax + 1):
        y = 2 * y + new.get(n, F(0))
        out.append(y)
        cut.append((2 * n // 3, 2 * n // 5))
    return out, cut


def atan_inv(m: int, bits: int) -> F:
    """arctan(1/m) to within 2^-bits, as an exact rational."""
    s, k = F(0), 0
    while True:
        term = F(1, (2 * k + 1) * m ** (2 * k + 1))
        if term < F(1, 2 ** bits):
            return s
        s += term if k % 2 == 0 else -term
        k += 1


def log2_rational(bits: int) -> F:
    """ln 2 = sum 1/(k 2^k) truncated with error below 2^-bits."""
    return sum((F(1, k * 2 ** k) for k in range(1, bits + 1)), F(0))


SERIES = [
    # key, label, theorem rate, status
    ("ln2", "ln 2, standard series", F(1), "lean"),
    ("atan", "arctan(1/2), Gaussian model", F(2, 3), "paper"),
    ("stride", "ln 2, half-rate series", F(1, 2), "lean"),
    ("dy2", "ln(4/3), k = 2", F(1, 2), "lean"),
    ("dy3", "ln(8/7), k = 3", F(1, 3), "lean"),
]


def sample_points(nmax: int) -> list[int]:
    """Every N up to 64, then a geometric grid with ratio about 1.012, ending at nmax."""
    pts = list(range(NMIN, 65))
    x = 64.0
    while True:
        x *= 1.012
        n = int(round(x))
        if n >= nmax:
            break
        if n > pts[-1]:
            pts.append(n)
    pts.append(nmax)
    return pts


def compute():
    n = NMAX
    pre = {
        "ln2": log_prefix(n),
        "stride": two_stride_prefix(n),
        "dy2": dyadic_log_prefix(2, n),
        "dy3": dyadic_log_prefix(3, n),
    }
    pre["atan"], cuts = gauss_prefix(n)
    den = {k: [y.denominator for y in v] for k, v in pre.items()}

    # --- agreement with the Lean definitions and finite Lean facts -------------------
    assert den["ln2"][10] == 63  # logDen_ten
    partial = F(0)
    for m in range(1, 41):  # shifted_partialLogTwo: 2^n * partialLogTwo n = logPrefix n
        partial += F(1, m * 2 ** m)
        assert 2 ** m * partial == pre["ln2"][m]
    for m in range(0, 61):  # twoStridePrefix definition = recurrence StrideDenominatorRate.step
        direct = strided_prefix_def(2, m, lambda _j: 2) + strided_prefix_def(3, m, lambda j: -(-1) ** j)
        assert direct == pre["stride"][m], m
    for k in (2, 3):  # dyadicLogPrefix_eq: = 2^N * Polylog.partialSum (2^k) 1 (N/k)
        for m in range(0, 61):
            ps = sum((F(1, (i + 1) * 2 ** (k * (i + 1))) for i in range(m // k)), F(0))
            assert 2 ** m * ps == pre[f"dy{k}"][m]
    for j in range(1, 17):  # the eight-periodic weight 1,1,1,0,-1,-1,-1,0
        assert gauss_weight(j) == [1, 1, 1, 0, -1, -1, -1, 0][(j - 1) % 8]

    lcm = [1]
    for m in range(1, n + 1):
        lcm.append(lcm[-1] * m // math.gcd(lcm[-1], m))
    primes = primes_upto(n)
    for m in range(1, n + 1):
        assert lcm[m] % den["ln2"][m] == 0  # logDen_dvd_lcm
        assert lcm[m // 2] % den["stride"][m] == 0  # twoStridePrefix_den
        assert lcm[m // 2] % den["dy2"][m] == 0  # Polylog.denominator_dvd, N/2
        assert lcm[m // 3] % den["dy3"][m] == 0  # Polylog.denominator_dvd, N/3
        assert lcm[cuts[m][0]] % den["atan"][m] == 0  # note: Q_N divides D_{M_2}
    for p in primes:  # twoStridePrefix_survival: odd p, 2p <= N < 3p  =>  p | den
        if p > 2:
            for m in range(2 * p, min(3 * p, n + 1)):
                assert den["stride"][m] % p == 0, (p, m)

    # error bounds at small N, with exact rational enclosures of the constants
    ln2 = log2_rational(400)
    atan_half = atan_inv(3, 400) + atan_inv(7, 400)
    assert abs(atan_half - atan_inv(2, 400)) < F(1, 2 ** 390)  # arctan 1/3 + arctan 1/7
    eps = F(1, 2 ** 390)
    for m in range(1, 301):
        e1 = 2 ** m * ln2 - pre["ln2"][m]  # logTwo_tail_bounds
        assert -eps * 2 ** m <= e1 <= F(1, m + 1) + eps * 2 ** m
        e2 = 2 ** m * ln2 - pre["stride"][m]  # twoStridePrefix_tail
        assert -eps * 2 ** m <= e2 <= F(4, m + 1) + eps * 2 ** m
        e3 = abs(2 ** m * atan_half - pre["atan"][m])
        assert e3 <= F(1, cuts[m][0] + 1) + F(1, cuts[m][1] + 1) + eps * 2 ** m

    # --- the plotted ratios -----------------------------------------------------------
    pts = sample_points(n)
    rate = {key: [ln_int(den[key][m]) / m for m in pts] for key, *_ in SERIES}
    for key, _label, r, _status in SERIES:  # curves trend toward the theorem rates
        tail = [ln_int(den[key][m]) / m for m in range(n - 400, n + 1)]
        mean = sum(tail) / len(tail)
        assert abs(mean - float(r)) < 0.03, (key, mean)
        assert abs(rate[key][-1] - float(r)) < 0.03, (key, rate[key][-1])
    exact_small = {key: den[key][:25] for key, *_ in SERIES}
    return {"points": pts, "rate": rate, "small": exact_small,
            "bits": {key: den[key][n].bit_length() for key, *_ in SERIES}}


def data_files(data):
    keys = [k for k, *_ in SERIES]
    lines = ["# (natural log of reduced denominator) / N for exact shifted binary prefixes",
             "# columns: " + ", ".join(f"{k} = {label} (rate {r}{', paper only' if s == 'paper' else ''})"
                                      for k, label, r, s in SERIES),
             "N," + ",".join(keys)]
    for i, m in enumerate(data["points"]):
        lines.append(f"{m}," + ",".join(f"{data['rate'][k][i]:.6f}" for k in keys))
    lines.append("# exact reduced denominators for N = 0..24")
    lines.append("N," + ",".join(keys))
    for m in range(25):
        lines.append(f"{m}," + ",".join(str(data["small"][k][m]) for k in keys))
    lines.append(f"# bit length of the denominator at N = {NMAX}: "
                 + ", ".join(f"{k} {data['bits'][k]}" for k in keys))
    return {"classical-denominator-growth.csv": "\n".join(lines) + "\n"}


# -- drawing --------------------------------------------------------------------------

STYLE = {
    # key: (stroke width, dash pattern)
    "ln2": (2.2, None),
    "atan": (1.8, "9 4 2 4"),
    "stride": (2.0, "7 4"),
    "dy2": (0, None),  # drawn as open markers
    "dy3": (2.0, "1.5 4"),
}


def render(data, t):
    W, H = 720, 560
    s = Svg(W, H, t, META["title"], META["alt"])
    s.heading("Denominator growth of classical prefixes",
              "q(N) is the reduced denominator of the shifted binary prefix at position N; natural log")
    s.badge("exact", y=62)
    x0, x1, y0, y1 = 72, 530, 104, 452
    X = log_scale(NMIN, NMAX, x0, x1)
    Y = lin_scale(0, 1.1, y1, y0)
    pts = data["points"]

    # certificate region: log q <= d log N
    region = [(X(m), Y(min(1.1, D_CERT * math.log(m) / m))) for m in pts]
    d = (f"M{fmt(x0)} {fmt(y1)} L" + " L".join(f"{fmt(a)} {fmt(b)}" for a, b in region)
         + f" L{fmt(x1)} {fmt(y1)} Z")
    s.path(d, fill=t.barrier, extra=' fill-opacity="0.22"')
    s.polyline(region, t.barrier, sw=1.6)
    s.line(x0, y1, x1, y1, t.barrier, sw=2.5)

    # grid and axes
    for v in (0.2, 0.4, 0.6, 0.8, 1.0):
        s.line(x0, Y(v), x1, Y(v), t.grid)
    for v in (0, 0.2, 0.4, 0.6, 0.8, 1.0):
        s.text(x0 - 10, Y(v) + 4.5, f"{v:g}", size=13, anchor="end", fill=t.ink2)
    for m in (32, 64, 128, 256, 512, 1024, 2048, 4096):
        s.line(X(m), y1, X(m), y1 + 5, t.rule)
        s.text(X(m), y1 + 22, str(m), size=13, anchor="middle", fill=t.ink2)
    s.axis_frame(x0, y0, x1, y1)
    s.text((x0 + x1) / 2, y1 + 44, "position N (logarithmic scale)", size=13, anchor="middle",
           fill=t.ink2)
    s.text(24, y0 - 14, "log q(N) / N", size=13, fill=t.ink2)

    # theorem rates as dotted reference lines, labelled at the right end
    for r, lab in ((1, "rate 1"), (2 / 3, "2/3 (paper)"), (1 / 2, "rate 1/2"), (1 / 3, "rate 1/3")):
        s.line(x0, Y(r), x1, Y(r), t.muted, sw=1, dash="2 3")

    # series curves in ink tones with distinct dash patterns
    for key, _label, _r, _st in SERIES:
        ys = data["rate"][key]
        line = [(X(m), Y(v)) for m, v in zip(pts, ys)]
        sw, dash = STYLE[key]
        colour = t.ink if key in ("ln2", "stride") else t.ink2
        if key == "dy2":
            for i in range(0, len(line), 9):
                s.circle(line[i][0], line[i][1], 3.2, t.surface, stroke=t.ink2, sw=1.4)
        else:
            s.polyline(line, colour, sw=sw, dash=dash)

    # direct labels to the right of the plot, with a short style key
    lx = x1 + 14

    def key_glyph(y, key):
        sw, dash = STYLE[key]
        if key == "dy2":
            for k in range(3):
                s.circle(lx + 3 + 8 * k, y - 4, 3, t.surface, stroke=t.ink2, sw=1.4)
        else:
            s.line(lx, y - 4, lx + 22, y - 4, t.ink if key in ("ln2", "stride") else t.ink2,
                   sw=sw, dash=dash)

    end = {key: data["rate"][key][-1] for key, *_ in SERIES}
    key_glyph(Y(end["ln2"]) + 2, "ln2")
    s.text(lx + 30, Y(end["ln2"]) + 2, "ln 2, standard", size=13)
    s.text(lx + 30, Y(end["ln2"]) + 19, "rate 1 · Lean", size=13, fill=t.ink2)

    ya = Y(2 / 3)
    key_glyph(ya - 4, "atan")
    s.text(lx + 30, ya - 4, "arctan(1/2)", size=13)
    s.text(lx + 30, ya + 13, "rate 2/3 · paper only", size=13, fill=t.ink2)

    yh = Y(0.5)
    key_glyph(yh - 10, "stride")
    s.text(lx + 30, yh - 10, "ln 2, half-rate", size=13)
    key_glyph(yh + 8, "dy2")
    s.text(lx + 30, yh + 8, "ln(4/3)", size=13)
    s.text(lx + 30, yh + 25, "both rate 1/2 · Lean", size=13, fill=t.ink2)

    y3 = Y(1 / 3)
    key_glyph(y3 + 2, "dy3")
    s.text(lx + 30, y3 + 2, "ln(8/7)", size=13)
    s.text(lx + 30, y3 + 19, "rate 1/3 · Lean", size=13, fill=t.ink2)

    # barrier label
    yb = Y(0.13)
    s.rect(lx, yb - 14, 14, 14, fill=t.barrier, rx=3)
    s.text(lx + 20, yb - 2, "certificate range", size=13)
    s.text(lx, yb + 15, f"log q ≤ {D_CERT} log N, fixed", size=13, fill=t.ink2)
    s.text(lx, yb + 31, "primes; rate 0 (AC-01)", size=13, fill=t.ink2)

    s.text(24, H - 34, "Dotted horizontal lines: theorem rates. Every point is an exact reduced "
                       "denominator (Fraction arithmetic).", size=12.5, fill=t.ink2)
    s.footer("Outside the certificate's hypotheses; no conclusion about normality of ln 2. "
             "Half-rate series: CC-01. Certificate: AC-01.")
    return s.done()
