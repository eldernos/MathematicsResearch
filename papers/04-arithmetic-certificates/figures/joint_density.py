"""Reproduce the two clipped intersection curves and their exact maxima."""
import csv
from fractions import Fraction as Q
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[2] / "scripts"))
from localized_certificate import certificate
from overlap_certificate import anchored_maximum, copies, failed_intervals, intersection_length


def vertices(p, fixed_pattern, q, other_pattern, cutoff):
    """List all changes in the order of an anchored and a moving band endpoint."""
    end = fixed_pattern[-1][1]
    fixed = sorted((max(cutoff, a), min(1, b))
                   for a, b in copies(p, fixed_pattern, Q(1) / end, cutoff)
                   if max(cutoff, a) < min(1, b))
    moving = sorted(copies(q, other_pattern, Q(1), cutoff))
    phases = {Q(1, q), Q(1)}
    for edges in fixed:
        for edge in edges:
            for bounds in moving:
                for bound in bounds:
                    if Q(1, q) < edge / bound < 1:
                        phases.add(edge / bound)
    points = [(u, intersection_length(fixed, moving, u)) for u in sorted(phases)]
    assert max((mass, u) for u, mass in points) == anchored_maximum(
        p, fixed_pattern, end, q, other_pattern, cutoff, (Q(1, q), Q(1)))
    return points


def main():
    primes = (5, 13)
    patterns = {p: failed_intervals(p, certificate(2, (2, *primes), p, 1)) for p in primes}
    assert patterns == {5: [(2, 4)], 13: [(10, 13)]}
    with (HERE / "joint_density.csv").open("w", newline="") as data:
        table = csv.writer(data, lineterminator="\n")
        table.writerow(("anchor_prime", "cutoff", "relative_scale", "clipped_length"))
        drawing = []
        for p, q in (primes, primes[::-1]):
            for cutoff in (Q(1, 10**5), Q(1, 10**10)):
                points = vertices(p, patterns[p], q, patterns[q], cutoff)
                table.writerows((p, cutoff, u, mass) for u, mass in points)
                u, mass = max(points, key=lambda pt: pt[1])
                if cutoff == Q(1, 10**5):
                    style = "anchorFive" if p == 5 else "anchorThirteen"
                    coords = "\n".join(f"({float(u):.9f},{float(m):.9f})" for u, m in points)
                    drawing.append(r"\draw[" + style + "] plot coordinates {\n" + coords + "\n};")
                    if p == 13:
                        drawing.append(r"\coordinate (jointPeak) at " + f"({float(u):.9f},{float(mass):.9f});")
                print(f"anchor {p}, cutoff {cutoff}, maximum {mass} at {u}")
    (HERE / "curves.tex").write_text("\n".join(drawing) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
