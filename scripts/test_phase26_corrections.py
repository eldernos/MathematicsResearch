"""Regression tests locking down the Phase 26 Stage 0.1 reporting precision corrections."""

from pathlib import Path
import tomllib
import unittest

ROOT = Path(__file__).resolve().parent.parent


def _load_gf() -> dict[str, dict]:
    data = tomllib.loads((ROOT / "docs" / "registry" / "GF.toml").read_text(encoding="utf-8"))
    return {entry["id"]: entry for entry in data["result"]}


def _load_cc() -> dict[str, dict]:
    data = tomllib.loads((ROOT / "docs" / "registry" / "CC.toml").read_text(encoding="utf-8"))
    return {entry["id"]: entry for entry in data["result"]}


def _load_families() -> dict[str, dict]:
    data = tomllib.loads(
        (ROOT / "docs" / "benchmarks" / "arithmetic-families.toml").read_text(encoding="utf-8")
    )
    return {entry["id"]: entry for entry in data["family"]}


def _load_constants() -> dict[str, dict]:
    data = tomllib.loads(
        (ROOT / "docs" / "benchmarks" / "classical-constants.toml").read_text(encoding="utf-8")
    )
    return {entry["id"]: entry for entry in data["constant"]}


class Phase26Stage01CorrectionsTest(unittest.TestCase):
    def test_gf42_signed_k0_and_b21_hypotheses(self) -> None:
        gf42 = _load_gf()["GF-42"]
        stmt = gf42["statement"]
        scope = gf42["scope"]
        self.assertIn("k ≥ k_0", stmt)
        self.assertIn("k ≥ k_0(χ)", stmt)
        self.assertIn("D^+(E_+(8); 2) < 1", stmt)
        self.assertIn("D^+(E_b^*(b^2); b) < 1", stmt)
        self.assertIn("valuation decomposition", stmt)
        self.assertIn("finite coefficient mass alone is insufficient", stmt)
        self.assertIn("k^{−1/2}", stmt)
        self.assertIn("k ≥ k_0", scope)

    def test_gf43_prime_subseries_not_complete_powers(self) -> None:
        gf43 = _load_gf()["GF-43"]
        stmt = gf43["statement"]
        self.assertIn("prime Fourier subseries", stmt)
        self.assertIn("do not classify the complete fourth, sixth, or eighth powers", stmt)

    def test_gf44_lp_ceiling_vs_sharper_mean_distinction(self) -> None:
        gf44 = _load_gf()["GF-44"]
        stmt = gf44["statement"]
        self.assertIn("17431/300000 = 0.0581033", stmt)
        self.assertIn("11477/187500 = 0.0612106", stmt)
        self.assertIn("not compared against the 0.059108 ceiling", stmt)
        self.assertNotIn("0.061210 (within 1.8%", stmt)
        self.assertNotIn("0.061210 on paper, within 1.8%", stmt)

    def test_gf45_single_radix_and_computability_scope(self) -> None:
        gf45 = _load_gf()["GF-45"]
        stmt = gf45["statement"]
        self.assertIn("does not assert one witness works simultaneously across multiple radices", stmt)
        self.assertIn("computably whenever α is computable", stmt)

    def test_gf47_e_purely_arithmetic(self) -> None:
        gf47 = _load_gf()["GF-47"]
        bc16 = _load_constants()["BC-16"]
        self.assertIn("purely arithmetic", gf47["statement"])
        self.assertIn("no new ordinary-radix normality or discrepancy classification", gf47["scope"])
        self.assertIn("purely arithmetic", bc16["notes"])

    def test_gf48_conditional_grh_and_kernel_boundary(self) -> None:
        gf48 = _load_gf()["GF-48"]
        scope = gf48["scope"]
        self.assertIn("preserve strict Conditional labels", scope)
        self.assertIn("not fully kernel-verified results of this repository", scope)

    def test_cc20_cc21_bc37_reconciled(self) -> None:
        cc20 = _load_cc()["CC-20"]
        cc21 = _load_cc()["CC-21"]
        bc37 = _load_constants()["BC-37"]
        self.assertEqual(bc37["discrepancy_status"], "open")
        self.assertEqual(bc37["digit_frequency_status"], "open")
        self.assertIn("residual", cc20["scope"])
        self.assertIn("residual", cc21["scope"])

    def test_frontier_and_bf26_no_signed_k3_overstatement(self) -> None:
        frontier = (ROOT / "docs" / "benchmarks" / "classical-family-frontier.md").read_text(
            encoding="utf-8"
        )
        bf26 = _load_families()["BF-26"]
        self.assertIn("*k*<sub>0</sub>", frontier)
        self.assertIn("0.0581033", frontier)
        self.assertNotIn("0.061210** (within 1.8%", frontier)
        self.assertIn("k ≥ k_0", bf26["summary"])
        self.assertIn("0.0581033", bf26["summary"])


if __name__ == "__main__":
    unittest.main()
