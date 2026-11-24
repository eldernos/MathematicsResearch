"""Figure 3: the finite-prime-support classification (LS-01) on representative cases.

``NormalityChecker.LocalizedSupport.unsigned_discrepancy_limit`` states, for b >= 2,
every order s >= 1 and every finite set P of primes, that the interval discrepancy
of X = sum over m in S of 1/(m^s b^m), where S is the set of positive integers whose
prime factors all lie in P, tends to

    1  if every q in P divides b,   0  otherwise.

The theorem allows P to be empty; then S = {1}, X = 1/b and the vacuous condition
gives the limit 1. The rows and columns are those of the Paper II classification
figure so that the README and the paper show the same cases.
"""

from __future__ import annotations

from svg import Svg

SLUG = "finite-support-classification"
META = {
    "number": 3,
    "summary": 'Normal or maximally discrepant: the limit of the interval discrepancy for each prime support and radix, as given by LS-01 for every order *s*.',
    "title": "Finite-prime-support classification matrix across representative radices",
    "caption": (
        "Each cell gives the limit of the interval discrepancy *D*ₙ of "
        "*X* = Σ 1/(*m*ˢ *b*ᵐ), summed over the positive integers *m* whose prime factors all lie "
        "in the support *P*, in base *b*. By the kernel-verified theorem LS-01 the limit is 0, so *X* is "
        "normal in base *b*, as soon as one prime of *P* does not divide *b*; it is 1, the maximal value, "
        "when every prime of *P* divides *b*. The same matrix holds for every positive integer order *s*. "
        "The empty support is covered by the theorem and is degenerate: then *X* = 1/*b* is rational and "
        "the limit is 1. The cells are a direct consequence of the theorem, not a computation of digits."
    ),
    "alt": (
        "Matrix with eight rows of prime supports (empty set, {2}, {3}, {5}, {2, 3}, {2, 5}, {3, 5}, "
        "{2, 3, 5}) and seven columns of radices (2, 3, 5, 6, 10, 15, 30). Cells labelled 0 are tinted aqua "
        "(normal); cells labelled 1 are tinted orange (maximal discrepancy). A 1 appears exactly when every "
        "prime of the support divides the radix: the whole empty-support row, the cells "
        "of {2} under radices 2, 6, 10 and 30, and the whole radix-30 column."
    ),
    "provenance": "theorem",
    "results": ["LS-01"],
    "sources": [
        "NormalityChecker.LocalizedSupport.unsigned_discrepancy_limit",
        "NormalityChecker/UnsignedNormality.lean",
        "notes/unsigned-finite-support.md",
    ],
}

SUPPORTS = [(), (2,), (3,), (5,), (2, 3), (2, 5), (3, 5), (2, 3, 5)]
BASES = [2, 3, 5, 6, 10, 15, 30]


def is_prime(n: int) -> bool:
    return n >= 2 and all(n % d for d in range(2, int(n ** 0.5) + 1))


def factor(n: int) -> list[int]:
    out, d = [], 2
    while n > 1:
        while n % d == 0:
            out.append(d)
            n //= d
        d += 1
    return out


def limit(base: int, support: tuple[int, ...]) -> int:
    """The limit in unsigned_discrepancy_limit: 1 if every q in P divides b, else 0."""
    return 1 if all(base % q == 0 for q in support) else 0


def support_label(support) -> str:
    return "{" + ", ".join(map(str, support)) + "}" if support else "∅"


def compute():
    assert all(is_prime(q) for P in SUPPORTS for q in P)  # hypothesis `primes`
    assert all(b >= 2 for b in BASES)  # hypothesis `hb`
    matrix = [[limit(b, P) for b in BASES] for P in SUPPORTS]
    # Agreement with the Paper II table (papers/02-localized-normality/figures/classification.csv).
    paper = ["1111111", "1001101", "0101011", "0010111", "0001001", "0000101", "0000011", "0000001"]
    assert ["".join(map(str, row)) for row in matrix] == paper
    # Equivalent formulation: the limit is 1 iff P is contained in the prime factors of b.
    for P, row in zip(SUPPORTS, matrix):
        for b, v in zip(BASES, row):
            assert v == int(set(P) <= set(factor(b)))
    return {"supports": SUPPORTS, "bases": BASES, "matrix": matrix}


def data_files(data):
    lines = ["support," + ",".join(map(str, data["bases"]))]
    for P, row in zip(data["supports"], data["matrix"]):
        label = "{" + " ".join(map(str, P)) + "}"
        lines.append(label + "," + ",".join(map(str, row)))
    return {"finite-support-classification.csv": "\n".join(lines) + "\n"}


def render(data, t):
    W, H = 720, 556
    s = Svg(W, H, t, META["title"], META["alt"])
    s.heading("Finite prime supports: normal or maximally discrepant",
              "Limit of the interval discrepancy of X = Σ 1/(mˢ bᵐ) over m with all prime factors in P")
    s.badge("theorem", y=68)

    bases, supports, matrix = data["bases"], data["supports"], data["matrix"]
    cw, ch = 64, 34
    x0 = 196
    y0 = 150
    xr = x0 + cw * len(bases)

    # column headers: radix and its factorisation
    s.text((x0 + xr) / 2, y0 - 46, "radix b", size=13, anchor="middle", fill=t.ink2)
    for j, b in enumerate(bases):
        cx = x0 + (j + 0.5) * cw
        s.text(cx, y0 - 22, str(b), size=15, anchor="middle", weight="600")
        f = factor(b)
        if len(f) > 1:
            s.text(cx, y0 - 7, "·".join(map(str, f)), size=12, anchor="middle", fill=t.muted)
    s.text(x0 - 16, y0 - 22, "support P", size=13, anchor="end", fill=t.ink2)

    for i, (P, row) in enumerate(zip(supports, matrix)):
        y = y0 + i * ch
        s.text(x0 - 16, y + ch / 2 + 5, support_label(P), size=14, anchor="end")
        if not P:
            s.text(x0 - 46, y + ch / 2 + 5, "X = 1/b", size=12, anchor="end", fill=t.muted)
        for j, v in enumerate(row):
            x = x0 + j * cw
            colour = t.resonance if v else t.normal
            s.rect(x + 2, y + 2, cw - 4, ch - 4, fill=colour, rx=4, opacity=0.42 if v else 0.26)
            s.rect(x + 2.5, y + 2.5, cw - 5, ch - 5, stroke=colour, sw=1.5, rx=4)
            s.text(x + cw / 2, y + ch / 2 + 5.5, str(v), size=15, anchor="middle",
                   weight="700" if v else "500")
    # separate the degenerate empty-support row
    s.line(x0 - 150, y0 + ch, xr, y0 + ch, t.rule, dash="3 3")

    yb = y0 + ch * len(supports)
    # legend
    ly = yb + 36
    for x, kind, label in ((x0 - 150, "normal", "0  normal in base b:  Dₙ → 0"),
                           (x0 + 160, "resonance", "1  maximal discrepancy:  Dₙ → 1")):
        colour = getattr(t, kind)
        s.rect(x, ly - 12, 18, 18, fill=colour, rx=4, opacity=0.30)
        s.rect(x + 0.5, ly - 11.5, 17, 17, stroke=colour, sw=1.5, rx=4)
        s.text(x + 26, ly + 2, label, size=13.5, fill=t.ink2)
    s.rich(x0 - 150, ly + 32, [("Rule: the limit is 1 exactly when every prime in ", False), ("P", True),
                                ("  divides  ", False), ("b", True), (".", False)], size=13.5, fill=t.ink)
    s.rich(x0 - 150, ly + 54, [("Holds for every order ", False), ("s", True), (" ≥ 1 and every radix ", False),
                                ("b", True), (" ≥ 2;  ∅ is the degenerate rational case.", False)],
           size=13.5, fill=t.ink2)
    s.footer("Lean: LocalizedSupport.unsigned_discrepancy_limit in UnsignedNormality.lean (LS-01).")
    return s.done()
