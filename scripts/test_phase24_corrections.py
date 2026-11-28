"""Regression tests locking down the 8 Phase 24 Stage 0.1 reporting precision corrections."""

from pathlib import Path
import tomllib
import unittest

ROOT = Path(__file__).resolve().parent.parent


def _load_gf() -> dict[str, dict]:
    data = tomllib.loads((ROOT / "docs" / "registry" / "GF.toml").read_text(encoding="utf-8"))
    return {entry["id"]: entry for entry in data["result"]}


def _load_families() -> dict[str, dict]:
    data = tomllib.loads(
        (ROOT / "docs" / "benchmarks" / "arithmetic-families.toml").read_text(encoding="utf-8")
    )
    return {entry["id"]: entry for entry in data["family"]}


class Phase24CorrectionsTest(unittest.TestCase):
    def test_gf36_stretched_series_and_limit_scope(self) -> None:
        gf36 = _load_gf()["GF-36"]
        stmt = gf36["statement"]
        scope = gf36["scope"]
        # Correction 1: D^-(E(2^k); 2) -> 1 is as k -> infinity, not D_N -> 1 for fixed k.
        self.assertIn("D^−(E(2^k); 2) → 1 as k → ∞", stmt)
        self.assertIn("not D_N → 1 for fixed k", stmt)
        # Correction 2: separate kernel-verified 29/(20k) from written/certified C_true/k.
        self.assertIn("29/(20k)", stmt)
        self.assertIn("C_true/k", stmt)
        self.assertIn("distinct from the stronger written-proof", stmt)
        # Correction 3: stretched series F_{2^k}(a) = sum a(n) 2^{-kn}, not F_2(a).
        self.assertIn("F_{2^k}(a) = Σ_{n ≥ 1} a(n) 2^{−kn}", stmt)
        self.assertNotIn("f_1(F_2(a); 2)", stmt)
        # Correction 4: distinguish tail-corrected carry counts from truncated-head carries.
        self.assertIn("integer tail correction", stmt)
        self.assertIn("truncated-head carry counts", stmt)
        self.assertIn("truncated-head carry counts", scope)
        # Correction 8: not a complete digit-distribution law; exact frequencies & discrepancy open.
        self.assertIn("rather than a complete digit-distribution law", stmt)
        self.assertIn("Exact limiting digit frequencies", scope)

    def test_gf39_regrouping_distinction(self) -> None:
        gf39 = _load_gf()["GF-39"]
        self.assertIn("exact geometric regrouping", gf39["statement"])
        self.assertIn("rather than a genuinely dense arithmetic proof", gf39["statement"])

    def test_gf40_eplus8_simple_vs_full(self) -> None:
        gf40 = _load_gf()["GF-40"]
        self.assertIn("simple nonnormality of E_+(8) remains open", gf40["statement"])
        self.assertIn("simple nonnormality of E_+(8)", gf40["scope"])

    def test_bf26_scope_and_k_limit(self) -> None:
        bf26 = _load_families()["BF-26"]
        self.assertIn("as k → ∞", bf26["summary"])
        self.assertIn("not D_N → 1 for fixed k", bf26["summary"])
        self.assertIn("simple normality of E_+(8) remains open", bf26["summary"])
        self.assertIn("Exact limiting digit frequencies", bf26["open_frontier"])

    def test_gf22_additive_cyclotomic_projection(self) -> None:
        gf22 = _load_gf()["GF-22"]
        self.assertIn("nonzero additive map Φ : ℤ[ζ_h] → ℤ", gf22["statement"])
        self.assertNotIn("every nonzero integer-valued function Φ", gf22["statement"])

    def test_research_objectives_multiplicatively_independent_qualified(self) -> None:
        text = (ROOT / "docs" / "research-objectives.md").read_text(encoding="utf-8")
        self.assertNotIn(
            "no explicit constant studied here is known to be normal in two multiplicatively independent bases",
            text,
        )
        self.assertIn("no classical constant studied here is known to be normal", text)
        self.assertIn("GF-39", text)


if __name__ == "__main__":
    unittest.main()
