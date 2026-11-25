"""Exact cycle spectra of the individual horizontal Taylor rows of log(2)."""
from fractions import Fraction
from math import gcd


def doubling_order(d):
    residue = 2 % d
    order = 1
    while residue != 1:
        residue = (2*residue) % d
        order += 1
    return order


def eventual_cycles(d):
    if d == 1:
        return [(Fraction(1),)]
    if d < 1 or d % 2 == 0:
        raise ValueError("d must be positive and odd")
    order = doubling_order(d)
    states, seen = [], {}
    phase, residue = 1 % order, 1
    while (phase, residue) not in seen:
        seen[phase, residue] = len(states)
        states.append(residue)
        residue = (pow(2, (d*phase + 1) % order, d)*residue + 1) % d
        phase = 2*phase % order
    laws = []
    for start in states[seen[phase, residue]:]:
        points = {start}
        z = 2*start % d
        while z != start:
            points.add(z)
            z = 2*z % d
        laws.append(tuple(Fraction(int(j in points), len(points)) for j in range(d)))
    return laws


def spectrum(d):
    laws = eventual_cycles(d)
    length = len(laws)
    low, high = Fraction(1), Fraction(0)
    for j, current in enumerate(laws):
        before = [sum((2**(length-i))*laws[(j-i) % length][r] for i in range(1, length+1))
                  / (2**length-1) for r in range(d)]
        # x in [0,1] runs from the start to the end of a shell, using
        # interpolation coefficient x/2 for its current cycle.
        lines = set()
        for start in range(d):
            base_mass = curr_mass = Fraction(0)
            for width in range(d):
                index = (start + width) % d
                base_mass += before[index]
                curr_mass += current[index]
                lines.add((base_mass-Fraction(width, d), (curr_mass-base_mass)/2))
        candidates = {Fraction(0), Fraction(1)}
        for a, b in lines:
            for c, e in lines:
                if b < 0 < e:
                    cross = (c-a)/(b-e)
                    if 0 < cross < 1:
                        candidates.add(cross)
        # If the minimum is a horizontal segment its ends may meet lines
        # of either sign. Include those breakpoints as well.
        for a, b in lines:
            if b == 0:
                for c, e in lines:
                    if e:
                        cross = (a-c)/e
                        if 0 < cross < 1:
                            candidates.add(cross)
        values = [max(a+b*x for a, b in lines) for x in candidates]
        low = min(low, min(values))
        high = max(high, max(values))
    return low, high


def main():
    for d in (1, 3, 5, 7, 9, 11):
        lo, hi = spectrum(d)
        print(f"odd part {d:2}: lower {lo}, upper {hi}")
        if d > 1:
            assert Fraction(1, d) <= lo <= hi <= 1-min(Fraction(1,6), Fraction(1,d))
            for j in range(9):
                exp = d*2**j+j
                num = sum(pow(2, exp-d*2**k-k, d) for k in range(j+1)) % d
                r = 1
                for k in range(j):
                    r = (pow(2, d*2**k+1, d)*r+1) % d
                assert num == r and gcd(2, d) == 1
    assert spectrum(1) == (1, 1)
    assert spectrum(3) == (Fraction(2,3), Fraction(2,3))
    assert spectrum(5) == (Fraction(1,5), Fraction(8,15))


if __name__ == "__main__":
    main()
