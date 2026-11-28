"""Regression tests locking the 8 Phase 23 consolidation corrections (Stage 0 of Phase 24)."""
from __future__ import annotations

import pathlib
import tomllib
import unittest

ROOT = pathlib.Path(__file__).resolve().parent.parent
GF_TOML = ROOT / "docs" / "registry" / "GF.toml"


def _load_gf() -> dict[str, dict]:
    data = tomllib.loads(GF_TOML.read_text(encoding="utf-8"))
    return {entry["id"]: entry for entry in data["result"]}


class Phase23CorrectionsTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.gf = _load_gf()

    def test_gf30_q_digamma_range_and_universal_sign_flip(self) -> None:
        stmt = self.gf["GF-30"]["statement"]
        self.assertIn("1 ≤ r < M/2", stmt)
        self.assertIn("r = M/2", stmt)
        self.assertIn("universal multiplicative sign-flip identity", stmt)

    def test_gf32_asymptotic_discrepancy_and_distinct_rates(self) -> None:
        stmt = self.gf["GF-32"]["statement"]
        self.assertNotIn("D_N(Y_b; b) ≤", stmt)
        self.assertIn("D^+(Y_b; b) ≤ 1 − 4/(15 b²)", stmt)
        self.assertIn("mean circular-distance rate m_N = O(N^{log_m 2 − 1})", stmt)
        self.assertIn("discrepancy-deficit rate 1 − D_N = O(N^{(log_m 2 − 1)/2})", stmt)

    def test_gf33_dense_representation_regrouping_qualification(self) -> None:
        stmt = self.gf["GF-33"]["statement"]
        self.assertIn("exact geometric regrouping", stmt)
        self.assertIn("not an arbitrary dense schedule", stmt)

    def test_gf34_per_base_scope_and_L_plus_1_clarification(self) -> None:
        stmt = self.gf["GF-34"]["statement"]
        self.assertIn("not one number acting simultaneously in all bases", stmt)
        self.assertIn("in fact (L + 1)-normal", stmt)
        self.assertIn("not of exact order L", stmt)

    def test_gf35_35_constant_map_scope(self) -> None:
        stmt = self.gf["GF-35"]["statement"]
        self.assertIn("whose tracked distributional fields are all currently open", stmt)


if __name__ == "__main__":
    unittest.main()
