"""Certify the first-precision ordinary failure bound after removing full rectangles."""
from fractions import Fraction
from bisect import bisect_right

from phase14_mixed_flow import cell_lengths, certify, flow_intervals, powers


def verify_cells(depth=4):
    scale = 81**2
    col_scale = 25**3
    phase = Fraction(col_scale, scale)
    cutoff = 81*scale
    threes, fives = powers(3,cutoff), powers(5,cutoff)
    bounds = []
    for outer in (False,True):
        intervals, unit = flow_intervals(phase, phase, depth, outer=outer, nonrectangular=True)
        assert unit % scale == 0
        bounds.append(cell_lengths(intervals, unit//scale,cutoff))
    borders = {0,*threes,*fives}
    tested = 0
    for n,(lo,hi) in enumerate(zip(*bounds)):
        if n in borders:
            continue
        k = bisect_right(threes,n)-1
        m = bisect_right(fives,n)-1
        p,q = threes[k], fives[m]
        # powers() includes 1, whereas the model begins at the positive exponents.
        top_row = max(0,bisect_right(fives,n-p)-1)
        top_col = max(0,bisect_right(threes,n-q)-1)
        bad = (top_row%2==0 and top_col%4==0 and n<p+q)
        expected = (unit//scale)*int(bad)
        assert lo <= expected <= hi, (n,lo,expected,hi)
        tested += 1
    return tested


if __name__ == '__main__':
    print('Direct integer cells:',verify_cells())
    lower, upper, phase, cutoff, boxes = certify(12,Fraction(1,10**13),nonrectangular=True)
    print('Lower:',lower,'Upper:',upper,'Witness phase and cutoff:',phase,cutoff,'Boxes:',boxes)
    print('Bounds:',float(lower),float(upper))
    assert upper-lower <= Fraction(1,10**13)
    assert Fraction(37047223953692, 10**14) < lower
    assert upper < Fraction(37047223953703, 10**14)
