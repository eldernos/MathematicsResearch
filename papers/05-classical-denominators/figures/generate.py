"""Reproduce the exact data, the vector plot, and the rows of Tables 1 and 2."""
import csv
from fractions import Fraction
from math import ceil, comb, floor, gcd, isqrt, lcm, log
from pathlib import Path
import sys

import cairo

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[2] / "scripts"))
from corrected_strides import adjacent_grid_example, cost_certificate, model, orders, sieve, sieve_selected, word_test
from discrepancy_experiments import log_bits
from localized_certificate import prime
from strided_logarithm import diagonal_sieve, low_transition_sieve, weight


def save(name, header, rows):
    with (HERE / name).open("w", newline="") as stream:
        out = csv.writer(stream, lineterminator="\n")
        out.writerow(header)
        out.writerows(rows)


def tex_rows(name, rows):
    with (HERE / name).open("w") as out:
        for row in rows:
            out.write(" & ".join(map(str, row)) + r" \\" + "\n")


def prefixes():
    standard = paired = Fraction(0)
    data = []
    for n in range(1, 1025):
        standard = 2 * standard + Fraction(1, n)
        paired = 2 * paired + Fraction(weight(n), n)
        if n >= 32 and n % 4 == 0:
            data.append((n, standard.denominator, paired.denominator))
    save("denominators.csv", ("binary_position", "standard_den", "two_stride_den"), data)
    return data


def draw(data):
    width, height = 484, 182
    pdf = cairo.PDFSurface(str(HERE / "denominators.pdf"), width, height)
    pdf.set_metadata(cairo.PDF_METADATA_CREATE_DATE, "2026-11-24T00:00:00Z")
    pdf.set_metadata(cairo.PDF_METADATA_MOD_DATE, "2026-11-24T00:00:00Z")
    cr = cairo.Context(pdf)
    cr.select_font_face("DejaVu Sans")
    cr.set_font_size(9)
    left, right, top, bottom = 44, 467, 26, 148

    def x(n):
        return left + (right-left) * (n-32) / (1024-32)

    def y(v):
        return bottom - (bottom-top)*v/1.1

    def label(xpos, ypos, s, align=0):
        ext = cr.text_extents(s)
        cr.move_to(xpos-align*ext.width, ypos)
        cr.show_text(s)

    cr.set_source_rgb(0.12, 0.14, 0.15)
    label(left, 13, "Natural logarithm of reduced denominator / binary position")
    label((left+right)/2, 178, "Binary position N", .5)
    for n in (32, 256, 512, 768, 1024):
        label(x(n), bottom+13, str(n), .5)
    for rate in (0, .25, .5, .75, 1):
        cr.set_source_rgb(.8,.81,.80)
        cr.set_dash([2, 3] if rate in (.5, 1) else [])
        cr.set_line_width(.6)
        cr.move_to(left, y(rate))
        cr.line_to(right, y(rate))
        cr.stroke()
        cr.set_dash([])
        cr.set_source_rgb(.12,.14,.15)
        label(left-7, y(rate)+3, f"{rate:g}", 1)
    for column, color, caption, text_y in (
        (1, (.10, .27, .42), "Standard series", y(.85)),
        (2, (.52, .20, .08), "Two-stride series", y(.36)),
    ):
        cr.set_source_rgb(*color)
        cr.set_line_width(1.15)
        for i, row in enumerate(data):
            n = row[0]
            (cr.move_to if i == 0 else cr.line_to)(x(n), y(log(row[column])/n))
        cr.stroke()
        label(right-5, text_y+2, caption, 1)
    pdf.finish()


def budgets():
    rows = []
    for h, rho, sigma, cap in [
        ("1/2", "0.08857", "0.07169", "0.746090"),
        ("1", "0.22365", "0.16931", "1.095663"),
        ("2", "0.58202", "0.40077", "1.962602"),
    ]:
        upper = cost_certificate(Fraction(h), Fraction(rho), Fraction(sigma))
        assert upper < Fraction(cap)
        rows.append((h, rho, sigma, cap, str(upper)))
    save("budgets.csv", ("horizon", "rho_2", "rho_3", "printed_upper_bound", "rational_upper_bound"), rows)
    tex_rows("budgets.tex", [row[:4] for row in rows])


def sieves():
    rows = []
    def record(family, n, t, a, cutoff, r, s, common, modulus, residue, error, survivors):
        words = 2 * sum(comb(t-1, i) for i in range(a+1))
        rows.append((family, n, t, a, cutoff, r, s, (common//modulus).bit_length(),
                     words, survivors, common, modulus, residue, str(error)))

    for n in (64, 128, 256, 512, 1024):
        common, modulus, residue = diagonal_sieve(n)
        bits, survivors = low_transition_sieve(n, n)
        assert bits == (common//modulus).bit_length()
        record("diagonal", n, n, 1, isqrt(2*n), n, "", common, modulus, residue,
               Fraction(1, (2*n+1)*comb(2*n, n)), survivors)
    for n, t, a, cutoff in ((128, 40, 2, 4), (256, 48, 2, 5),
                             (512, 64, 3, 5), (1024, 80, 3, 7)):
        r, s = orders(n, t)
        corrected = model(n, r, s)
        modulus, residue = sieve(corrected, cutoff)
        r1, s1, bits, survivors = word_test(n, t, a, cutoff)
        assert (r, s, (corrected.common//modulus).bit_length()) == (r1, s1, bits)
        record("two-stride", n, t, a, cutoff, r, s, corrected.common, modulus, residue,
               corrected.error, survivors)
    save("sieves.csv", ("model", "n", "T", "changes", "cutoff", "order_1", "order_2",
                        "lift_bits", "word_count", "survivors", "L", "P", "residue", "error"), rows)
    tex_rows("sieves.tex", [(row[0], *row[1:5],
                             f"{row[5]},{row[6]}" if row[6] != "" else row[5], *row[7:10])
                            for row in rows])

def overlap():
    t = 64
    grids = []
    for n, omitted, advance in ((512, {2, 3, 5}, 2), (513, {2, 3, 7}, 1)):
        data = model(n, *orders(n, t))
        tested = (p for p in range(2, len(data.weights)) if p not in omitted and prime(p))
        modulus, residue = sieve_selected(data, tested)
        size = data.common // modulus
        grids.append((advance*Fraction(residue, data.common), size//gcd(advance, size),
                      advance*data.error))
    (u, h, e1), (v, k, e2) = grids
    m, g = lcm(h, k), gcd(h, k)
    jmin = ceil(m*(v-u-e1-e2))
    jmax = floor(m*(v-u+e1+e2))
    assert 2*m*(e1+e2) < 1 and jmin == jmax
    # Solve (k/g) i - (h/g) j = jmin. All other compatible pairs
    # are simultaneous translations of both solutions by a multiple of 1/g.
    i = (jmin*pow(k//g, -1, h//g)) % (h//g)
    j, rem = divmod((k//g)*i-jmin, h//g)
    assert rem == 0
    left_center, right_center = u + Fraction(i,h), v + Fraction(j,k)
    low = max(left_center-e1, right_center-e2)
    high = min(left_center+e1, right_center+e2)
    assert low <= high and (h, k, g) == adjacent_grid_example()
    scale = 1 << t
    admitted = set()
    for a in range(g):
        shift = Fraction(a, g)
        for word in range(ceil(scale*(low+shift))-1, floor(scale*(high+shift))+1):
            admitted.add(word % scale)
    counts = [0]*t
    for word in admitted:
        difference = (word ^ (word >> 1)) & ((1 << (t-1))-1)
        counts[difference.bit_count()] += 1
    actual = log_bits(513+t)[513:]
    assert len(actual) == t and int(actual, 2) in admitted
    actual_changes = sum(left != right for left, right in zip(actual, actual[1:]))
    save("overlap.csv", ("first_start", "second_start", "word_length", "advanced_h", "k",
                         "compatible_pairs", "intersection_lower", "intersection_upper",
                         "certified_binary_word", "actual_changes"),
         [(512, 513, t, h, k, g, str(low), str(high), actual, actual_changes)])
    save("overlap_words.csv", ("transitions", "admitted_words"), enumerate(counts))


if __name__ == "__main__":
    draw(prefixes())
    budgets()
    sieves()
    overlap()
