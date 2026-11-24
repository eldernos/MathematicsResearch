"""Regenerate three vector illustrations and their exact data with Python 3."""
from collections import Counter
from fractions import Fraction
from pathlib import Path
import csv

HERE = Path(__file__).resolve().parent


def save_rows(name, header, records):
    with (HERE / name).open("w", newline="") as out:
        writer = csv.writer(out, lineterminator="\n")
        writer.writerow(header)
        writer.writerows(records)


def lattice():
    threshold = Fraction(10, 9)
    points = []
    for i in range(5):
        for j in range(5):
            included = Fraction(1, 3**i) + Fraction(1, 3**j) <= threshold
            points.append((i, j, int(included)))
    save_rows("lattice.csv", ("i", "j", "included"), points)
    lines = [r"\begin{tikzpicture}[x=.59cm,y=.59cm,font=\small]",
             r"\fill[bluegreen!9] (-.22,1.78) -- (.78,1.78) -- (.78,.78) -- (1.78,.78) -- (1.78,-.22) -- (4.4,-.22) -- (4.4,4.4) -- (-.22,4.4) -- cycle;",
             r"\draw[step=1,black!12] (0,0) grid (4,4);"]
    for i, j, included in points:
        if included:
            lines.append(rf"\fill[bluegreen] ({i},{j}) circle (2.1pt);")
        else:
            lines.append(rf"\draw[black!45,fill=white] ({i},{j}) circle (2pt);")
    for i, j in [(0, 2), (1, 1), (2, 0)]:
        lines.append(rf"\draw[bluegreen,thick] ({i},{j}) circle (4pt);")
    lines += [r"\foreach \i in {0,...,4} {\node[below] at (\i,-.25) {\i}; \node[left] at (-.25,\i) {\i};}",
              r"\node at (2,-1.2) {$i$}; \node at (-1.1,2) {$j$};", r"\end{tikzpicture}"]
    (HERE / "lattice.tex").write_text("\n".join(lines) + "\n")


def square():
    limit = 242
    jumps = Counter()
    i = 3
    while i <= limit:
        j = 3
        while i + j <= limit:
            jumps[i + j] += Fraction(1, i * j)
            j *= 3
        i *= 3
    prefix = Fraction(0)
    data = []
    previous = None
    segments = []
    for n in range(limit + 1):
        prefix = 2 * prefix + jumps[n]
        den = prefix.denominator
        exponent = 0
        while den % 3 == 0:
            den //= 3
            exponent += 1
        assert den == 1
        data.append((n, prefix.denominator, exponent))
        if exponent != previous:
            segments.append((n, exponent))
        previous = exponent
    save_rows("square.csv", ("n", "denominator", "exponent"), data)
    lines = [r"\begin{tikzpicture}[x=.043cm,y=.30cm,font=\footnotesize]",
             r"\fill[orange!13] (30,0) rectangle (36,8.7);",
             r"\foreach \i in {0,2,4,6,8} {\draw[black!15] (0,\i) -- (243,\i); \node[left] at (0,\i) {\i};}",
             r"\foreach \i in {0,30,54,81,108,162,243} {\draw (\i,-.14) -- (\i,0); \node[below] at (\i,-.14) {\i};}",
             r"\draw[->] (0,0) -- (252,0) node[right] {$n$};",
             r"\node[anchor=south west] at (0,8.8) {$v_3(q_n)$};"]
    for index, (lo, exponent) in enumerate(segments):
        hi = segments[index + 1][0] if index + 1 < len(segments) else limit + 1
        lines += [rf"\draw[bluegreen,very thick] ({lo},{exponent}) -- ({hi},{exponent});",
                  rf"\fill[bluegreen] ({lo},{exponent}) circle (1.4pt);",
                  rf"\draw[bluegreen,fill=white] ({hi},{exponent}) circle (1.3pt);"]
    lines.append(r"\end{tikzpicture}")
    (HERE / "square.tex").write_text("\n".join(lines) + "\n")


def joint():
    # For all n<N, the floor at scale 2^(N+1) determines the first
    # two digits of 2^n times the value. Certify that floor once per power.
    N = 4096
    scale = 1 << (N + 1)
    prefix = Fraction(0)
    power = 3
    while True:
        prefix += Fraction(1, power * (1 << power))
        power *= 3
        # The sum of all subsequent 3^-j is 3/(2*power).
        upper = prefix + Fraction(3, 2 * power * (1 << power))
        lo = [int(scale * prefix**r) for r in (1, 2)]
        hi = [int(scale * upper**r) for r in (1, 2)]
        if lo == hi:
            break
    counts = Counter(((lo[0] >> (N-1-n)) & 3, (lo[1] >> (N-1-n)) & 3) for n in range(N))
    save_rows("joint.csv", ("first_pair", "square_pair", "count"),
              ((i, j, counts[i, j]) for i in range(4) for j in range(4)))
    lines = [r"\begin{tabular}{c@{\qquad}rrrr}\toprule",
             r"&\multicolumn{4}{c}{Word in $\alpha^2$}\\",
             r"Word in $\alpha$ & 00 & 01 & 10 & 11 \\ \midrule"]
    for i in range(4):
        lines.append(f"{i:02b} & " + " & ".join(str(counts[i, j]) for j in range(4)) + r" \\")
    lines += [r"\bottomrule\end{tabular}"]
    (HERE / "joint.tex").write_text("\n".join(lines) + "\n")


if __name__ == "__main__":
    lattice()
    square()
    joint()
