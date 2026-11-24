"""Figure 2: the exact 3-adic exponent of the reduced denominator of the shifted
rational prefix of the binary Stoneham square, for every digit position below 3^9.

The prefix is the Lean definition ``NormalityChecker.StonehamSquare.pre``:

    pre n = sum over ordered pairs (i, j), i, j >= 1, with 3^i + 3^j <= n,
            of 2^(n - 3^i - 3^j) / 3^(i + j).

(Lean indexes from zero; its ``location`` (i, j) = 3^(i+1) + 3^(j+1) is the same
set of insertions.) The prefix is not reduced modulo one; its reduced denominator
is unaffected by integer parts anyway.

``compute`` evaluates the denominator three independent ways and asserts that they
agree at every position:

1. the Lean definition, read through ``numerator`` / ``scaled_pre``: pre n equals
   numerator(n, D) / 3^D for the largest active degree D, so the reduced denominator
   is 3^D / gcd(numerator mod 3^D, 3^D), computed with exact modular integers;
2. the rational recurrence R_n = 2 R_(n-1) + sum over 3^i + 3^j = n of 3^-(i+j),
   in exact ``Fraction`` arithmetic (the independent check named in the note);
3. the closed forms of the Lean theorems ``initial_profile`` (n < 81) and
   ``exact_profile`` (every scale 3^k <= n < 3^(k+1), k >= 4).

It also asserts ``third_scale_exception``, the exact values R_30, R_35, R_36
quoted in notes/stoneham-square.md, and ``quadratic_denominator``.
"""

from __future__ import annotations

from fractions import Fraction as F
from math import gcd, log

from svg import Svg, lin_scale, log_scale

SLUG = "stoneham-square-denominator"
META = {
    "number": 2,
    "summary": 'The exact exponent of 3 in the shifted denominators of the Stoneham square: it grows by two per geometric scale, with one cancelled factor on a fixed part of each scale (ST-03).',
    "title": "Exact denominator exponent landscape across multiple geometric scales",
    "caption": (
        "For every digit position 1 ≤ *n* < 3⁹ the blue step line is the exponent of 3 in the "
        "reduced denominator *q*ₙ of the shifted rational prefix *R*ₙ of α², which keeps exactly "
        "the products of terms whose insertion position 3ⁱ + 3ʲ is at most *n*. Every value is an "
        "exact rational computation (each *q*ₙ is a power of 3), checked at all 19 683 positions "
        "0 ≤ *n* < 3⁹ against an independent "
        "recurrence and against the closed form proved in Lean: on each scale 3ᵏ ≤ *n* < 3ᵏ⁺¹ "
        "with *k* ≥ 4 the exponent is 2*k* − 2, 2*k* − 3, 2*k* − 1 and 2*k* on four intervals "
        "starting at 3ᵏ, 3ᵏ + 3ᵏ⁻², 3ᵏ + 3ᵏ⁻¹ and 2·3ᵏ. Orange marks the intervals where one "
        "factor of 3 cancels, and the small-scale exception *q*ₙ = 9 for 30 ≤ *n* < 36. The grey "
        "band is the kernel-verified bound *n*²/243 < *q*ₙ ≤ *n*² for *n* ≥ 81 (ST-03)."
    ),
    "alt": (
        "Two step charts. The upper chart has a logarithmic horizontal axis of digit position n "
        "from 1 to 19683, with vertical lines at the powers of 3, and a vertical axis from 0 to 18 "
        "giving the exponent of 3 in the reduced denominator. The blue step line starts at 0, "
        "jumps to 2 at n = 6, 3 at 12 and 4 at 18, drops to 2 on the orange interval from 30 to "
        "35, then rises by about two per power of 3 up to 16, staying inside a grey band between "
        "the lines 2 log base 3 of n minus 5 and 2 log base 3 of n. On each scale from 81 on, a "
        "narrow orange interval marks a dip of one. The lower chart enlarges the scale from 729 "
        "to 2187 on a linear axis: the exponent is 10 from 729, drops to 9 from 810 (orange), is "
        "11 from 972 and 12 from 1458 up to 2187."
    ),
    "provenance": "exact",
    "results": ["ST-03"],
    "sources": [
        "NormalityChecker.StonehamSquare.pre",
        "NormalityChecker.StonehamSquare.exact_profile",
        "NormalityChecker.StonehamSquare.initial_profile",
        "NormalityChecker.StonehamSquare.third_scale_exception",
        "NormalityChecker.StonehamSquare.quadratic_denominator",
        "notes/stoneham-square.md",
    ],
}

TOP = 9            # positions 0 <= n < 3^TOP
LIMIT = 3 ** TOP
ZOOM = 6           # scale enlarged in the lower panel


def v3(m: int) -> int:
    e = 0
    while m % 3 == 0:
        m //= 3
        e += 1
    return e


def pairs(limit: int):
    """Ordered index pairs (i, j), i, j >= 1, with location 3^i + 3^j < limit."""
    out = []
    i = 1
    while 3 ** i < limit:
        j = 1
        while 3 ** i + 3 ** j < limit:
            out.append((3 ** i + 3 ** j, i + j))
            j += 1
        i += 1
    return sorted(out)


def lean_denominator(n: int, ps) -> int:
    """Reduced denominator of ``pre n`` via ``scaled_pre``: pre n = numerator(n, D) / 3^D."""
    act = [(loc, deg) for loc, deg in ps if loc <= n]          # mem_active: location <= n
    if not act:
        return 1
    D = max(deg for _, deg in act)
    mod = 3 ** D
    num = sum(pow(2, n - loc, mod) * 3 ** (D - deg) for loc, deg in act) % mod
    return mod // gcd(num, mod)


def closed_form(n: int) -> int:
    """``initial_profile`` for n < 81 and ``exact_profile`` (scale index k = K + 4) beyond."""
    if n < 81:
        for stop, den in ((6, 1), (12, 9), (18, 27), (30, 81), (36, 9), (54, 243), (81, 729)):
            if n < stop:
                return den
    k = 0
    while 3 ** (k + 1) <= n:
        k += 1
    P = 3 ** k
    if n < P + 3 ** (k - 2):
        return 3 ** (2 * k - 2)
    if n < P + 3 ** (k - 1):
        return 3 ** (2 * k - 3)
    if n < 2 * P:
        return 3 ** (2 * k - 1)
    return 3 ** (2 * k)


def compute():
    ps = pairs(LIMIT)
    jumps: dict[int, F] = {}
    for loc, deg in ps:
        jumps[loc] = jumps.get(loc, F(0)) + F(1, 3 ** deg)
    R = F(0)
    exps = []
    for n in range(LIMIT):
        R = 2 * R + jumps.get(n, 0)                      # independent recurrence
        q = R.denominator
        assert 3 ** v3(q) == q, (n, q)                   # pure power of three
        assert q == lean_denominator(n, ps) == closed_form(n), n
        if n == 30:
            assert R == F(16952434, 9)
        elif n == 35:
            assert R == F(542477888, 9)
        elif n == 36:
            assert R == F(29293805954, 243)
        if n >= 81:                                      # quadratic_denominator
            assert n * n < 243 * q and q <= n * n, n
        exps.append(v3(q))
    runs = []
    for n, e in enumerate(exps):
        if runs and runs[-1][2] == e:
            runs[-1][1] = n + 1
        else:
            runs.append([n, n + 1, e])
    dips = [(3 ** k + 3 ** (k - 2), 3 ** k + 3 ** (k - 1)) for k in range(4, TOP)]
    for a, b in dips:
        assert exps[a - 1] == exps[a] + 1 and exps[b] == exps[a] + 2
    return {"runs": runs, "dips": dips, "exception": (30, 36)}


def rule(start: int) -> str:
    if start < 81:
        return "initial_profile"
    k = 0
    while 3 ** (k + 1) <= start:
        k += 1
    P = 3 ** k
    names = {P: "2k-2", P + 3 ** (k - 2): "2k-3", P + 3 ** (k - 1): "2k-1", 2 * P: "2k"}
    return f"exact_profile k={k} exponent {names[start]}"


def data_files(data):
    lines = ["start,stop_exclusive,v3_denominator,reduced_denominator,lean_rule"]
    for a, b, e in data["runs"]:
        lines.append(f"{a},{b},{e},{3 ** e},{rule(a)}")
    return {"stoneham-square-denominator.csv": "\n".join(lines) + "\n"}


# -- rendering ---------------------------------------------------------------
SUP = str.maketrans("0123456789", "⁰¹²³⁴⁵⁶⁷⁸⁹")


def render(data, t):
    W, H = 720, 700
    shade = 0.28 if t.name == "light" else 0.42
    s = Svg(W, H, t, META["title"], META["alt"])
    s.heading("Exact denominator profile of the Stoneham square",
              "Exponent of 3 in the reduced denominator qₙ of the shifted prefix of α² at digit n")
    s.badge("exact", y=78)
    runs, dips = data["runs"], data["dips"]

    # ---- upper panel: every scale on a logarithmic axis --------------------
    x0, x1, y0, y1 = 64, W - 28, 128, 368
    X = log_scale(1, LIMIT, x0, x1)
    Y = lin_scale(0, 18, y1, y0)
    for e in range(0, 19, 2):
        s.line(x0, Y(e), x1, Y(e), t.grid)
        s.text(x0 - 8, Y(e) + 4.5, str(e), size=13, anchor="end", fill=t.ink2)
    for k in range(TOP + 1):
        s.line(X(3 ** k), y0, X(3 ** k), y1, t.grid if k else t.rule)
        lab = "1" if k == 0 else "3" + str(k).translate(SUP)
        s.text(X(3 ** k), y1 + 19, lab, size=13, anchor="middle", fill=t.ink2)
    s.text((x0 + x1) / 2, y1 + 42, "digit position n (logarithmic; vertical lines at powers of 3)",
           size=13, anchor="middle", fill=t.ink2)
    s.text(x0 - 46, y0 - 14, "exponent of 3 in qₙ", size=13, fill=t.ink2)
    # Lean quadratic bounds 2 log3 N - 5 < v <= 2 log3 N for N >= 81
    l3 = lambda n: log(n) / log(3)
    band = [(X(81), Y(2 * l3(81))), (X(LIMIT), Y(2 * l3(LIMIT))),
            (X(LIMIT), Y(2 * l3(LIMIT) - 5)), (X(81), Y(2 * l3(81) - 5))]
    s.path("M" + " L".join(f"{x:.2f} {y:.2f}" for x, y in band) + " Z", fill=t.grid, stroke=t.rule)
    # cancellation intervals
    for a, b in dips + [data["exception"]]:
        s.rect(X(a), y0, X(b) - X(a), y1 - y0, fill=t.resonance, opacity=shade)
    # step line
    pts = []
    for a, b, e in runs:
        lo = max(a, 1)
        pts += [(X(lo), Y(e)), (X(b), Y(e))]
    s.polyline(pts, t.exact, sw=2.2)
    # zoom bracket on scale 6
    za, zb = 3 ** ZOOM, 3 ** (ZOOM + 1)
    s.path(f"M{X(za):.2f} {y1 - 6} V{y1} H{X(zb):.2f} V{y1 - 6}", stroke=t.ink2, sw=1.5)
    # legend (upper-left, where the profile is low) and the small-scale exception
    lx, ly = x0 + 14, y0 + 22
    s.line(lx, ly - 4, lx + 18, ly - 4, t.exact, sw=2.4)
    s.text(lx + 26, ly + 1, "exact exponent of 3 in qₙ", size=13, fill=t.ink2)
    s.rect(lx, ly + 12, 18, 14, fill=t.resonance, opacity=shade)
    s.text(lx + 26, ly + 24, "one factor of 3 cancels", size=13, fill=t.ink2)
    s.rect(lx, ly + 35, 18, 14, fill=t.grid, stroke=t.rule)
    s.text(lx + 26, ly + 47, "Lean bound n²/243 < qₙ ≤ n², n ≥ 81", size=13, fill=t.ink2)
    s.line(X(33), Y(8.6), X(33), Y(4.6), t.ink2)
    s.text(X(33), Y(9.6) - 2, "small-scale exception", size=13, anchor="middle", fill=t.ink2)
    s.text(X(33), Y(9.6) - 18, "30 ≤ n < 36: qₙ = 9", size=13, anchor="middle")

    # ---- lower panel: one scale on a linear axis ---------------------------
    P = za
    k = ZOOM
    zx0, zx1, zy0, zy1 = 64, W - 28, 470, 620
    Xz = lin_scale(P, 3 * P, zx0, zx1)
    lo_e, hi_e = 2 * k - 4, 2 * k + 1
    Yz = lin_scale(lo_e, hi_e, zy1, zy0)
    s.text(24, zy0 - 36, f"Enlarged: the scale 3{str(k).translate(SUP)} = {P} ≤ n < "
           f"3{str(k + 1).translate(SUP)} = {3 * P} (k = {k})", size=14, weight="600")
    for e in range(lo_e, hi_e + 1):
        s.line(zx0, Yz(e), zx1, Yz(e), t.grid)
        s.text(zx0 - 8, Yz(e) + 4.5, str(e), size=13, anchor="end", fill=t.ink2)
    cuts = [P, P + 3 ** (k - 2), P + 3 ** (k - 1), 2 * P, 3 * P]
    for c in cuts:
        s.line(Xz(c), zy0, Xz(c), zy1, t.rule)
        s.text(Xz(c), zy1 + 19, str(c), size=13, anchor="middle", fill=t.ink2)
    s.rect(Xz(cuts[1]), zy0, Xz(cuts[2]) - Xz(cuts[1]), zy1 - zy0, fill=t.resonance, opacity=shade)
    zr = [(a, b, e) for a, b, e in runs if b > P and a < 3 * P]
    pts = []
    for a, b, e in zr:
        pts += [(Xz(max(a, P)), Yz(e)), (Xz(min(b, 3 * P)), Yz(e))]
    s.polyline(pts, t.exact, sw=2.4)
    labels = ["2k − 2", "2k − 3", "2k − 1", "2k"]
    for (a, b, e), lab in zip(zr, labels):
        cx = (Xz(max(a, P)) + Xz(min(b, 3 * P))) / 2
        if lab == "2k − 2":
            s.text(Xz(P) + 6, Yz(e) - 8, f"{lab} = {e}", size=13)
        elif lab == "2k − 3":
            s.text(cx, Yz(e) + 19, f"{lab} = {e}", size=13, anchor="middle")
        else:
            s.text(cx, Yz(e) - 8, f"{lab} = {e}", size=13, anchor="middle")
    s.text((zx0 + zx1) / 2, zy1 + 40, "digit position n (linear)", size=13, anchor="middle",
           fill=t.ink2)
    s.footer("Checked at every n < 3⁹ against Lean exact_profile, initial_profile and "
             "third_scale_exception (ST-03).")
    return s.done()
