"""Regression tests locking the four Phase 22 consolidation corrections.

Correction 1 (GF-26): ord_{D(b^m + 1)}(b) = 2m whenever D | b^m - 1 (not 2mD).
Correction 2 (GF-28, BC-39): a_+(n) = (1 - v_2(n)) tau_odd(n) (not 1 - 2 v_2(n)).
Correction 3 (GF-19, GF-20, Paper XI): construction-radix scope (not "any base").
Correction 4 (GF-25, BF-20): explicit prime/degree/order-budget hypotheses for Theorem G.
"""

from __future__ import annotations

import pathlib
import unittest

ROOT = pathlib.Path(__file__).resolve().parent.parent


def mult_order(b: int, mod: int) -> int:
    val = b % mod
    k = 1
    while val != 1:
        val = (val * b) % mod
        k += 1
    return k


def v2(n: int) -> int:
    e = 0
    while n % 2 == 0:
        n //= 2
        e += 1
    return e


def tau_odd(n: int) -> int:
    odd = n >> v2(n)
    return sum(1 for d in range(1, odd + 1) if odd % d == 0)


class Phase22CorrectionsTest(unittest.TestCase):
    def test_correction1_plus_sign_period_exact(self) -> None:
        # Concrete counterexample to 2mD: b=2, m=2, D=3 => D(b^m+1)=15, ord_15(2)=4=2m != 12.
        self.assertEqual(mult_order(2, 3 * (2**2 + 1)), 4)
        for b in (2, 3, 5, 6):
            for m in range(1, 6):
                bm_minus = b**m - 1
                for D in range(1, min(bm_minus, 40) + 1):
                    if bm_minus % D == 0:
                        self.assertEqual(mult_order(b, D * (b**m + 1)), 2 * m)

        gf_text = (ROOT / "docs/registry/GF.toml").read_text(encoding="utf-8")
        gf26 = gf_text.split('id = "GF-26"', 1)[1].split("[[result]]", 1)[0]
        self.assertIn("ord_{D(b^m + 1)}(b) = 2 m whenever D ∣ b^m − 1", gf26)
        self.assertNotIn("2 m D whenever 2 D", gf26)

    def test_correction2_plus_erdos_borwein_coeff_exact(self) -> None:
        # E_+(b) = sum_{n>=1} 1/(b^n + 1) = sum_{n>=1} a_+(n) b^{-n},
        # where a_+(n) = sum_{d|n} (-1)^{d-1} = (1 - v_2(n)) tau_odd(n).
        for n in range(1, 200):
            alt_sum = sum((-1) ** (d - 1) for d in range(1, n + 1) if n % d == 0)
            self.assertEqual(alt_sum, (1 - v2(n)) * tau_odd(n))
            self.assertEqual(alt_sum == 0, n % 4 == 2)

        gf_text = (ROOT / "docs/registry/GF.toml").read_text(encoding="utf-8")
        gf28 = gf_text.split('id = "GF-28"', 1)[1]
        self.assertIn("(1 − v_2(n)) τ_odd(n)", gf28)
        self.assertNotIn("1 − 2 v_2(n)", gf28)

        bc_text = (ROOT / "docs/benchmarks/classical-constants.toml").read_text(encoding="utf-8")
        bc39 = bc_text.split('id = "BC-39"', 1)[1].split("[[constant]]", 1)[0]
        self.assertIn("(1 − v_2(n)) τ_odd(n)", bc39)
        self.assertNotIn("1 − 2 v_2(n)", bc39)

    def test_correction3_radix_scope_precision(self) -> None:
        gf_text = (ROOT / "docs/registry/GF.toml").read_text(encoding="utf-8")
        gf19 = gf_text.split('id = "GF-19"', 1)[1].split("[[result]]", 1)[0]
        gf20 = gf_text.split('id = "GF-20"', 1)[1].split("[[result]]", 1)[0]
        self.assertNotIn("never simply normal in any base", gf19)
        self.assertNotIn("never simply normal in any base", gf20)
        self.assertIn("construction radix b", gf20)

        p11 = (ROOT / "papers/11-generating-functions-digits/paper.tex").read_text(encoding="utf-8")
        self.assertNotIn("not simply normal in any base", p11)

    def test_correction4_gf25_hypotheses_explicit(self) -> None:
        gf_text = (ROOT / "docs/registry/GF.toml").read_text(encoding="utf-8")
        gf25 = gf_text.split('id = "GF-25"', 1)[1].split("[[result]]", 1)[0]
        self.assertIn("p > (r + 1)!", gf25)
        self.assertIn("(P_G)", gf25)
        self.assertIn("λ ≥ r + 1", gf25)


if __name__ == "__main__":
    unittest.main()
