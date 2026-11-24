#!/usr/bin/env python3
"""Regenerate the manuscript's exact rational data and TikZ drawings."""
import csv
import math
from fractions import Fraction
from itertools import product
from pathlib import Path

HERE = Path(__file__).resolve().parent


def save_table(name, header, rows):
    with (HERE / name).open("w", newline="", encoding="utf-8") as stream:
        writer = csv.writer(stream, lineterminator="\n")
        writer.writerow(header)
        writer.writerows(rows)


def save_drawing(name, lines):
    (HERE / name).write_text("\n".join(lines + [r"\end{tikzpicture}", ""]),
                             encoding="utf-8")


def prefix():
    # The binary (p=3) expansion with c=(1,0,1,0,...), translated by 1/3.
    first, last = 3, 9
    zero_count = 0
    samples = []
    for j in range(last):
        left, right = 3**j, 3**(j+1)
        is_zero = j % 2
        if first <= j:
            for i in range(24):
                cutoff = left + i * (right-left) // 24
                count = zero_count + (cutoff-left) * is_zero
                density = Fraction(count, cutoff)
                samples.append((cutoff, count, density, Fraction(2, 3) * density))
        zero_count += (right-left) * is_zero
    end = 3**last
    density = Fraction(zero_count, end)
    samples.append((end, zero_count, density, Fraction(2, 3) * density))
    save_table("prefix.csv", ("N", "Z(N)", "Z(N)/N", "(2/3)Z(N)/N"), samples)

    lines = [r"\begin{tikzpicture}[x=1.64cm,y=3.0cm,font=\small]"]
    for j in range(first, last):
        if j % 2:
            lines.append(rf"\fill[ink!7] ({j},0) rectangle ({j+1},.84);")
    for y, label in [(0, "0"), (.25, "1/4"), (.5, "1/2"), (.75, "3/4")]:
        lines.append(rf"\draw[black!20] ({first},{y}) -- ({last},{y});")
        lines.append(rf"\node[left] at ({first},{y}) {{\({label}\)}};")
    for j in range(first, last+1):
        lines.append(rf"\draw ({j},0) -- ++(0,-.017) node[below] {{\({j}\)}};")
    lines.append(r"\node[below] at (6,-.12) {\(\log_3 N\)};")
    for column, style in [(2, "ink,thick"), (3, "ochre,thick,dashed")]:
        coords = [f"({math.log(row[0], 3):.6f},{float(row[column]):.6f})"
                  for row in samples]
        lines.append(rf"\draw[{style}] plot coordinates {{")
        lines.extend(" ".join(coords[start:start+8]) for start in range(0, len(coords), 8))
        lines.append("};")
    lines.append(r"\node[anchor=west,text=ink] at (9,.29) {\(Z(N)/N\)};")
    lines.append(r"\node[anchor=west,text=ochre] at (9,.12) {\(\frac23 Z(N)/N\)};")
    save_drawing("prefix.tex", lines)


def spectrum():
    rows = []
    points = {2: set(), 3: set()}
    for length in range(1, 9):
        for bits in product("01", repeat=length):
            word = "".join(bits)
            # A whole period ending at each residue yields all reverse rotations.
            reverse = word[::-1]
            maximal = max(reverse[i:] + reverse[:i] for i in range(length))
            values = []
            for p in points:
                integer = (p-1) * int(maximal, p)
                value = Fraction(integer, p**length-1)
                values.append(value)
                points[p].add(value)
            rows.append((length, word, maximal, *values))
    save_table("spectrum.csv", ("length", "chronological_zero_bits", "max_reverse_rotation",
                                "p=2", "p=3"), rows)

    lines = [r"\begin{tikzpicture}[x=11.2cm,y=1cm,font=\small]"]
    for p, y in [(2, .95), (3, .45)]:
        lines.append(rf"\draw[black!22] (0,{y}) -- (1,{y});")
        lines.append(rf"\node[left] at (-.015,{y}) {{\(p={p}\)}};")
        for value in sorted(points[p]):
            lines.append(rf"\draw[ink,line width=.5pt] ({float(value):.7f},{y-.105:.3f}) "
                         rf"-- ++(0,.21);")
    for value, label in [(0, "0"), (.25, "1/4"), (.5, "1/2"), (.75, "3/4"), (1, "1")]:
        lines.append(rf"\draw ({value},.22) -- ++(0,-.055) node[below] {{\({label}\)}};")
    save_drawing("spectrum.tex", lines)


if __name__ == "__main__":
    prefix()
    spectrum()
