"""Unit tests for the benchmark schema checks and progress table (docs/benchmarks/SCHEMA.md).

Each test mutates a deep copy of the real benchmark data and asserts that
``portal.check_benchmarks`` reports the expected violation, so every mechanical
rule of the schema is exercised on the data it actually guards.
"""

import copy
import unittest

import portal

C_FILE = portal.BENCH_C_FILE
F_FILE = portal.BENCH_F_FILE


class BenchmarkCase(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.ids = portal.check_registry([], [])
        cls.c_data, cls.f_data = portal.load_benchmarks()

    def data(self):
        return copy.deepcopy(self.c_data), copy.deepcopy(self.f_data)

    def const(self, c, bid):
        return next(e for e in c["constant"] if e["id"] == bid)

    def fam(self, f, bid):
        return next(e for e in f["family"] if e["id"] == bid)

    def errors(self, c, f):
        errs = []
        portal.check_benchmarks(self.ids, errs, c, f)
        return errs

    def assertRejected(self, c, f, fragment, where=None):
        errs = self.errors(c, f)
        hits = [e for e in errs if fragment in e and (where is None or where in e)]
        self.assertTrue(hits, f"expected an error containing {fragment!r} (at {where}); got {errs}")

    @staticmethod
    def rec(radix="base 2", prop="digit_frequency_status", status="nontrivial_bound", evidence="external",
            source="Someone 1990: a theorem"):
        return {"radix": radix, "property": prop, "status": status, "evidence": evidence, "source": source}


class RealDataTests(BenchmarkCase):
    def test_current_files_pass(self):
        self.assertEqual(self.errors(*self.data()), [])

    def test_roster_is_fixed(self):
        c, f = self.data()
        self.assertEqual([e["id"] for e in c["constant"]], [f"BC-{i:02d}" for i in range(1, 51)])
        self.assertEqual([e["id"] for e in f["family"]], [f"BF-{i:02d}" for i in range(1, 26)])
        self.assertEqual(c["meta"]["schema_version"], 2)
        self.assertEqual(f["meta"]["schema_version"], 2)

    def test_control_cohort(self):
        c, _ = self.data()
        control = {e["id"] for e in c["constant"] if e["cohort"] == "control"}
        self.assertEqual(control, set(portal.BENCH_CONTROL_IDS))
        self.assertEqual(control, {"BC-33", "BC-34", "BC-40", "BC-45", "BC-46", "BC-47", "BC-48", "BC-49"})

    def test_e2_square_digit_bound_tracked_separately(self):
        c, _ = self.data()
        e = self.const(c, "BC-29")
        self.assertEqual(e["simple_normality"], "open")
        self.assertEqual(e["digit_frequency_status"], "nontrivial_bound")
        self.assertEqual(e["evidence"], "lean+paper")
        rec = next(r for r in e["radix_results"] if r["property"] == "digit_frequency_status")
        self.assertEqual((rec["radix"], rec["evidence"]), ("base 2", "paper"))
        self.assertIn("GF-20", rec["source"])
        self.assertIn("GF-27", rec["source"])


    def test_minor_citation_fixes(self):
        c, f = self.data()
        bc29 = self.const(c, "BC-29")
        fn = next(r for r in bc29["radix_results"] if r["property"] == "full_normality")
        self.assertIn("GF-04", fn["source"])
        self.assertIn("GF-12", fn["source"])
        bc50 = self.const(c, "BC-50")
        self.assertIn("ST-27", bc50["registry_ids"])
        dj = next(r for r in bc50["radix_results"] if r["property"] == "disjunctivity")
        self.assertIn("ST-27", dj["source"])
        self.assertIn("ST-32", dj["source"])
        self.assertIn("ST-29", bc50["notes"])
        self.assertIn("4631/12500", bc50["notes"])
        bf03 = self.fam(f, "BF-03")
        self.assertEqual(bf03["digit_frequency_status"], "partial")
        self.assertIn("digit_frequency_status = partial", bf03["summary"])
        self.assertIn("lower frequency at least 0.136", bf03["summary"])

    def test_no_status_changes_in_reproved_controls(self):
        c, _ = self.data()
        for bid, fields in {
            "BC-34": ("proved_nonnormal", "proved_not_simply_normal", "proved_disjunctive", "maximal_K_b"),
            "BC-40": ("proved_nonnormal", "proved_not_simply_normal", "proved_disjunctive", "maximal_K_b"),
            "BC-49": ("proved_normal", "proved_simply_normal", "proved_disjunctive", "zero_normal"),
        }.items():
            e = self.const(c, bid)
            self.assertEqual(tuple(e[k] for k in portal.BENCH_STATUS_FIELDS), fields, bid)


class MetaAndFieldTests(BenchmarkCase):
    def test_schema_version_1_rejected(self):
        c, f = self.data()
        c["meta"]["schema_version"] = 1
        self.assertRejected(c, f, "invalid [meta]", C_FILE)
        c, f = self.data()
        f["meta"]["schema_version"] = 1
        self.assertRejected(c, f, "invalid [meta]", F_FILE)

    def test_missing_new_fields_rejected(self):
        for field in ("cohort", "control_provenance", "digit_frequency_status", "radix_results"):
            c, f = self.data()
            del self.const(c, "BC-10")[field]
            self.assertRejected(c, f, "field mismatch", "BC-10")
        c, f = self.data()
        del self.fam(f, "BF-10")["digit_frequency_status"]
        self.assertRejected(c, f, "field mismatch", "BF-10")

    def test_families_have_no_radix_results(self):
        c, f = self.data()
        self.fam(f, "BF-01")["radix_results"] = []
        self.assertRejected(c, f, "field mismatch", "BF-01")

    def test_enum_values(self):
        c, f = self.data()
        self.const(c, "BC-10")["cohort"] = "reference"
        self.assertRejected(c, f, "invalid cohort", "BC-10")
        c, f = self.data()
        self.const(c, "BC-10")["digit_frequency_status"] = "partial"
        self.assertRejected(c, f, "invalid digit_frequency_status", "BC-10")
        c, f = self.data()
        self.fam(f, "BF-13")["digit_frequency_status"] = "bounded"
        self.assertRejected(c, f, "invalid digit_frequency_status", "BF-13")


class CohortTests(BenchmarkCase):
    def test_cohort_is_fixed(self):
        c, f = self.data()
        self.const(c, "BC-27")["cohort"] = "control"
        self.assertRejected(c, f, "fixed control cohort", "BC-27")
        c, f = self.data()
        self.const(c, "BC-33")["cohort"] = "unresolved"
        self.assertRejected(c, f, "fixed control cohort", "BC-33")

    def test_control_needs_decided_normality(self):
        c, f = self.data()
        e = self.const(c, "BC-45")
        e.update(full_normality="open", simple_normality="open", disjunctivity="open",
                 discrepancy_status="open", digit_frequency_status="open", barrier_status="no_barrier_recorded",
                 evidence="open")
        self.assertRejected(c, f, "control constant has full_normality decided", "BC-45")

    def test_control_provenance_shape(self):
        c, f = self.data()
        self.const(c, "BC-47")["control_provenance"] = {}
        self.assertRejected(c, f, "control_provenance needs exactly the string keys", "BC-47")
        c, f = self.data()
        self.const(c, "BC-47")["control_provenance"] = "Champernowne 1933"
        self.assertRejected(c, f, "control_provenance must be an inline table", "BC-47")
        c, f = self.data()
        self.const(c, "BC-27")["control_provenance"] = copy.deepcopy(self.const(c, "BC-47")["control_provenance"])
        self.assertRejected(c, f, "control_provenance must be {} for an unresolved constant", "BC-27")
        c, f = self.data()
        self.const(c, "BC-47")["control_provenance"]["basis"] = "explicit_digits"
        self.assertRejected(c, f, "differs from the fixed basis", "BC-47")
        c, f = self.data()
        self.const(c, "BC-33")["control_provenance"]["basis"] = "folklore"
        self.assertRejected(c, f, "invalid basis", "BC-33")

    def test_theorem_control_needs_pre_program_source(self):
        c, f = self.data()
        self.const(c, "BC-47")["control_provenance"]["source"] = "Someone 2026: normality in base 10"
        self.assertRejected(c, f, "every year in it must precede 2026", "BC-47")
        c, f = self.data()
        self.const(c, "BC-47")["control_provenance"]["source"] = "Champernowne: normality in base 10"
        self.assertRejected(c, f, "source needs a four-digit year", "BC-47")
        c, f = self.data()
        self.const(c, "BC-47")["control_provenance"]["source"] = "Champernowne 1953: normality in base 10"
        self.assertRejected(c, f, "every cited year must belong to a pre-2026 entry of external_sources", "BC-47")

    def test_incidental_early_number_in_2026_citation_rejected(self):
        # m6.1: a 2026 citation does not pass on an incidental number in 1500..2025.
        c, f = self.data()
        e = self.const(c, "BC-47")
        e["external_sources"].append("Someone 2026: a proof that uses the integer 1729")
        e["control_provenance"]["source"] = "Someone 2026: a proof that uses the integer 1729"
        self.assertRejected(c, f, "every year in it must precede 2026", "BC-47")

    def test_theorem_control_source_names_no_registry_entry(self):
        c, f = self.data()
        self.const(c, "BC-49")["control_provenance"]["source"] = "Stoneham 1973 and ST-01"
        self.assertRejected(c, f, "a published-theorem source names no registry entry", "BC-49")

    def test_positive_simple_normality_is_not_a_control_witness(self):
        # M3: proved_simply_normal does not decide full normality.
        c, f = self.data()
        self.const(c, "BC-49")["control_provenance"].update(
            property="simple_normality", status="proved_simply_normal",
            source="Stoneham 1973: proved simply normal only")
        self.assertRejected(c, f, "must decide full_normality or record simple_normality=proved_not_simply_normal",
                            "BC-49")
        c, f = self.data()
        self.const(c, "BC-49")["control_provenance"].update(property="disjunctivity", status="proved_disjunctive")
        self.assertRejected(c, f, "must decide full_normality", "BC-49")
        # A negative simple normality decision and a full normality decision both qualify.
        c, f = self.data()
        self.assertEqual(self.const(c, "BC-34")["control_provenance"]["status"], "proved_not_simply_normal")
        self.assertEqual(self.const(c, "BC-47")["control_provenance"]["property"], "full_normality")
        self.assertEqual([x for x in self.errors(c, f) if "BC-34" in x or "BC-47" in x], [])

    def test_control_provenance_matches_entry(self):
        c, f = self.data()
        self.const(c, "BC-49")["control_provenance"]["status"] = "proved_nonnormal"
        self.assertRejected(c, f, "differs from full_normality", "BC-49")

    def test_control_provenance_strings_checked(self):
        c, f = self.data()
        self.const(c, "BC-45")["control_provenance"]["source"] = "digits | positions"
        self.assertRejected(c, f, "forbidden character in source", "BC-45")

    def test_explicit_digit_control_needs_no_year_or_record(self):
        c, f = self.data()
        e = self.const(c, "BC-45")
        self.assertEqual(e["radix_results"], [])
        self.assertEqual(e["control_provenance"]["basis"], "explicit_digits")
        self.assertEqual([x for x in self.errors(c, f) if "BC-45" in x], [])

    def test_unresolved_constants_have_empty_provenance(self):
        c, _ = self.data()
        for e in c["constant"]:
            self.assertEqual(bool(e["control_provenance"]), e["cohort"] == "control", e["id"])


class ControlProvenanceSeparationTests(BenchmarkCase):
    """M4: radix_results records current evidence; pre-program provenance is separate."""

    def test_reproved_controls_record_repository_evidence(self):
        c, _ = self.data()
        want = {"BC-34": ("simple_normality", "lean+paper"), "BC-40": ("simple_normality", "lean+paper"),
                "BC-49": ("full_normality", "lean")}
        for bid, (prop, ev) in want.items():
            e = self.const(c, bid)
            self.assertFalse([r for r in e["radix_results"] if r["evidence"] == "external"], bid)
            self.assertEqual(portal.bench_property_evidence(e, prop), ev, bid)
            self.assertEqual(e["evidence"], ev, bid)
            self.assertEqual(e["control_provenance"]["basis"], "published_theorem", bid)
            self.assertTrue(portal.bench_is_pre_program(e["control_provenance"]["source"]), bid)

    def test_external_scope_record_weaker_than_entry_rejected(self):
        c, f = self.data()
        self.const(c, "BC-49")["radix_results"] = [self.rec(
            prop="full_normality", status="proved_normal",
            source="Stoneham 1973 and Bailey–Crandall 2002: normality of α(2, 3) in base 2")]
        self.assertRejected(c, f, "weaker than the entry-level evidence=lean", "BC-49")
        c, f = self.data()
        self.const(c, "BC-34")["radix_results"] = [self.rec(
            prop="simple_normality", status="proved_not_simply_normal",
            source="Bailey–Borwein–Crandall–Pomerance 2004: the digit 1 has frequency 0")]
        self.assertRejected(c, f, "weaker than the entry-level evidence=lean+paper", "BC-34")

    def test_external_record_allowed_when_property_rests_on_external_input(self):
        c, f = self.data()
        e = self.const(c, "BC-47")
        self.assertEqual(e["evidence"], "external")
        self.assertEqual([r["evidence"] for r in e["radix_results"]], ["external"])
        self.assertEqual([x for x in self.errors(c, f) if "BC-47" in x], [])

    def test_uncovered_digit_bound_record_may_be_weaker(self):
        # A single-base nontrivial_bound is not covered by the entry-level label.
        c, f = self.data()
        e = self.const(c, "BC-29")
        self.assertEqual(portal.bench_property_evidence(e, "digit_frequency_status"), "paper")
        self.assertEqual(e["evidence"], "lean+paper")
        self.assertEqual([x for x in self.errors(c, f) if "BC-29" in x], [])

    def test_progress_tables_agree_on_reproved_controls(self):
        c, f = self.data()
        text = portal.build_benchmarks_progress(c, f)
        lines = text.splitlines()
        radix = text.split("## Per-radix and per-property results", 1)[1].split("## Arithmetic families", 1)[0]
        for bid, label in (("BC-34", "Lean-supported paper proof"), ("BC-40", "Lean-supported paper proof"),
                           ("BC-49", "Kernel-verified")):
            const_row = next(x for x in lines if x.startswith(f"| {bid} |") and "| control |" in x)
            self.assertIn(f"| {label} |", const_row)
            radix_rows = [x for x in radix.splitlines() if x.startswith(f"| {bid} |")]
            self.assertTrue(radix_rows, bid)
            for row in radix_rows:
                self.assertIn(f"| {label} |", row)
                self.assertNotIn("External input", row)
        prov = text.split("### Pre-program classification of the control constants", 1)[1].split("## Counts", 1)[0]
        row49 = next(x for x in prov.splitlines() if x.startswith("| BC-49 |"))
        self.assertIn("(External input)", row49)
        self.assertTrue(row49.endswith("| Kernel-verified |"))
        row47 = next(x for x in prov.splitlines() if x.startswith("| BC-47 |"))
        self.assertTrue(row47.endswith("| — (not proved in the repository) |"))
        self.assertEqual(sum(1 for x in prov.splitlines() if x.startswith("| BC-")), 8)


class DigitFrequencyTests(BenchmarkCase):
    def test_simply_normal_requires_exact_law(self):
        c, f = self.data()
        self.const(c, "BC-27")["digit_frequency_status"] = "nontrivial_bound"
        self.assertRejected(c, f, "proved_simply_normal requires digit_frequency_status=exact_law", "BC-27")
        c, f = self.data()
        self.fam(f, "BF-01")["digit_frequency_status"] = "partial"
        self.assertRejected(c, f, "proved_simply_normal requires digit_frequency_status=exact_law", "BF-01")

    def test_not_simply_normal_requires_law_or_bound(self):
        c, f = self.data()
        self.const(c, "BC-28")["digit_frequency_status"] = "open"
        self.assertRejected(c, f, "proved_not_simply_normal requires", "BC-28")
        c, f = self.data()
        self.fam(f, "BF-21")["digit_frequency_status"] = "partial"
        self.assertRejected(c, f, "proved_not_simply_normal requires", "BF-21")

    def test_exact_law_requires_decided_simple_normality(self):
        c, f = self.data()
        self.const(c, "BC-29")["digit_frequency_status"] = "exact_law"
        self.assertRejected(c, f, "exact_law requires decided simple_normality", "BC-29")
        c, f = self.data()
        self.fam(f, "BF-08")["digit_frequency_status"] = "exact_law"
        self.assertRejected(c, f, "exact_law requires decided simple_normality", "BF-08")

    def test_partial_simple_normality_requires_non_open(self):
        c, f = self.data()
        self.fam(f, "BF-04")["digit_frequency_status"] = "open"
        self.assertRejected(c, f, "simple_normality=partial requires", "BF-04")

    def test_classified_simple_normality(self):
        c, f = self.data()
        e = self.fam(f, "BF-04")
        e["simple_normality"] = "classified"
        self.assertRejected(c, f, "simple_normality=classified requires", "BF-04")
        e["digit_frequency_status"] = "classified"
        self.assertEqual([x for x in self.errors(c, f) if "BF-04" in x], [])

    def test_family_bound_requires_evidence(self):
        # M2: a family whose four status fields are open can carry a digit-frequency result.
        c, f = self.data()
        e = self.fam(f, "BF-13")
        e["digit_frequency_status"] = "partial"
        self.assertRejected(c, f, "evidence=open iff all five distributional fields", "BF-13")
        for ev in ("paper", "external"):
            e["evidence"] = ev
            self.assertEqual([x for x in self.errors(c, f) if "BF-13" in x], [], ev)
        e["digit_frequency_status"] = "open"
        self.assertRejected(c, f, "evidence=open iff all five distributional fields", "BF-13")

    def test_family_bound_with_lean_evidence_still_needs_lean_entry(self):
        c, f = self.data()
        e = self.fam(f, "BF-13")
        e.update(digit_frequency_status="nontrivial_bound", evidence="lean")
        self.assertRejected(c, f, "evidence=lean requires a listed lean registry entry", "BF-13")

    def test_all_bases_constant_bound_requires_entry_evidence(self):
        # M1: an all-bases bound has no scope-radix record, so evidence must not stay open.
        c, f = self.data()
        e = self.const(c, "BC-01")
        self.assertEqual(e["radices_scope"], "all integer bases b ≥ 2")
        e["digit_frequency_status"] = "nontrivial_bound"
        self.assertEqual((e["evidence"], e["radix_results"]), ("open", []))
        self.assertRejected(c, f, "evidence=open iff all five distributional fields", "BC-01")
        e["evidence"] = "external"
        self.assertEqual([x for x in self.errors(c, f) if "BC-01" in x], [])
        self.assertEqual(portal.bench_property_evidence(e, "digit_frequency_status"), "external")

    def test_single_base_bound_evidence_stays_in_record(self):
        c, f = self.data()
        e = self.const(c, "BC-31")
        e["digit_frequency_status"] = "nontrivial_bound"
        e["radix_results"] = [self.rec(source="Someone 1990: positive lower frequency of the digit 1")]
        e["evidence"] = "external"
        self.assertRejected(c, f, "evidence=open iff all four status fields are open", "BC-31")

    def test_nontrivial_bound_requires_scope_record(self):
        c, f = self.data()
        e = self.const(c, "BC-29")
        e["radix_results"] = [r for r in e["radix_results"] if r["property"] != "digit_frequency_status"]
        self.assertRejected(c, f, "nontrivial_bound requires a radix_results record", "BC-29")

    def test_bound_with_all_fields_open_is_allowed_with_record(self):
        c, f = self.data()
        e = self.const(c, "BC-31")
        e["digit_frequency_status"] = "nontrivial_bound"
        self.assertRejected(c, f, "nontrivial_bound requires a radix_results record", "BC-31")
        e["radix_results"] = [self.rec(source="Someone 1990: positive lower frequency of the digit 1")]
        self.assertEqual([x for x in self.errors(c, f) if "BC-31" in x], [])


class RadixResultTests(BenchmarkCase):
    def mutate(self, bid, record):
        c, f = self.data()
        self.const(c, bid)["radix_results"] = [record]
        return c, f

    def test_type_and_fields(self):
        c, f = self.data()
        self.const(c, "BC-10")["radix_results"] = "none"
        self.assertRejected(c, f, "list of inline tables", "BC-10")
        r = self.rec()
        del r["source"]
        self.assertRejected(*self.mutate("BC-10", r), "field mismatch", "BC-10")
        self.assertRejected(*self.mutate("BC-10", dict(self.rec(), radix=3)), "every field must be a string", "BC-10")

    def test_radix_property_status_evidence_values(self):
        self.assertRejected(*self.mutate("BC-10", self.rec(radix="base 1")), "radix must be", "BC-10")
        self.assertRejected(*self.mutate("BC-10", self.rec(radix="all integer bases b ≥ 2")), "radix must be", "BC-10")
        self.assertRejected(*self.mutate("BC-10", self.rec(prop="barrier_status", status="resolved")),
                            "invalid property", "BC-10")
        self.assertRejected(*self.mutate("BC-10", self.rec(status="open")), "invalid status", "BC-10")
        self.assertRejected(*self.mutate("BC-10", self.rec(prop="simple_normality", status="radix_dependent")),
                            "invalid status", "BC-10")
        self.assertRejected(*self.mutate("BC-10", self.rec(evidence="open")), "invalid evidence", "BC-10")
        self.assertRejected(*self.mutate("BC-10", self.rec(source="  ")), "empty source", "BC-10")

    def test_duplicate_records(self):
        c, f = self.data()
        self.const(c, "BC-10")["radix_results"] = [self.rec(radix="base 3"), self.rec(radix="base 3")]
        self.assertRejected(c, f, "duplicate record", "BC-10")

    def test_forbidden_characters_and_unknown_ids(self):
        self.assertRejected(*self.mutate("BC-10", self.rec(source="Someone 1990: x | y")),
                            "forbidden character in source", "BC-10")
        self.assertRejected(*self.mutate("BC-10", self.rec(source="Someone 1990: $x$")),
                            "forbidden character in source", "BC-10")
        self.assertRejected(*self.mutate("BC-10", self.rec(evidence="paper", source="GF-99")),
                            "unknown inline registry id GF-99", "BC-10")

    def test_source_registry_ids_must_be_listed(self):
        self.assertRejected(*self.mutate("BC-10", self.rec(evidence="paper", source="GF-20")),
                            "not in registry_ids", "BC-10")

    def test_evidence_against_named_entries(self):
        c, f = self.data()
        e = self.const(c, "BC-50")
        dfr = next(r for r in e["radix_results"] if r["property"] == "digit_frequency_status")
        dfr["source"] = "a written step only"
        self.assertRejected(c, f, "requires a registry identifier in source", "BC-50")
        c, f = self.data()
        disc = next(r for r in self.const(c, "BC-50")["radix_results"] if r["property"] == "discrepancy_status")
        disc["source"] = "ST-06 and ST-32"
        self.assertRejected(c, f, "evidence=lean requires every named registry entry", "BC-50")
        c, f = self.data()
        disc = next(r for r in self.const(c, "BC-50")["radix_results"] if r["property"] == "discrepancy_status")
        disc["evidence"] = "lean+paper"
        self.assertRejected(c, f, "evidence=lean+paper requires", "BC-50")
        c, f = self.data()
        rec = self.const(c, "BC-37")["radix_results"][0]
        rec["source"] = "Captain Sude, release without a date"
        self.assertRejected(c, f, "evidence=external requires a four-digit year", "BC-37")

    def test_scope_radix_record_matches_entry(self):
        c, f = self.data()
        rec = next(r for r in self.const(c, "BC-29")["radix_results"] if r["property"] == "full_normality")
        rec["status"] = "proved_normal"
        self.assertRejected(c, f, "differs from full_normality", "BC-29")

    def test_all_bases_record_agrees_with_decided_value(self):
        c, f = self.data()
        e = self.const(c, "BC-01")
        e["disjunctivity"] = "proved_disjunctive"
        e["evidence"] = "external"
        e["radix_results"] = [self.rec(radix="base 3", prop="disjunctivity", status="proved_non_disjunctive")]
        self.assertRejected(c, f, "contradicts the all-bases value", "BC-01")

    def test_single_radix_result_without_overclaiming(self):
        # Simple nonnormality in base 3 while the all-bases scope stays open.
        c, f = self.data()
        e = self.const(c, "BC-01")
        e["radix_results"] = [self.rec(radix="base 3", prop="simple_normality", status="proved_not_simply_normal")]
        self.assertRejected(c, f, "requires full_normality=proved_nonnormal in the same radix", "BC-01")
        e["radix_results"].append(self.rec(radix="base 3", prop="full_normality", status="proved_nonnormal"))
        self.assertEqual([x for x in self.errors(c, f) if "BC-01" in x], [])
        self.assertEqual(e["simple_normality"], "open")

    def test_other_radix_record_for_single_base_scope(self):
        c, f = self.data()
        e = self.const(c, "BC-49")
        e["radix_results"].append(self.rec(radix="base 3", prop="full_normality", status="proved_normal"))
        e["radix_results"].append(self.rec(radix="base 3", prop="disjunctivity", status="proved_non_disjunctive"))
        self.assertRejected(c, f, "proved_normal conflicts with disjunctivity", "BC-49")

    def test_radix_dependent_needs_two_records(self):
        c, f = self.data()
        e = self.const(c, "BC-01")
        e.update(simple_normality="radix_dependent", digit_frequency_status="nontrivial_bound", evidence="external")
        e["radix_results"] = [
            self.rec(radix="base 2", prop="simple_normality", status="proved_simply_normal"),
        ]
        self.assertRejected(c, f, "radix_dependent requires radix_results records", "BC-01")
        e["radix_results"] += [
            self.rec(radix="base 3", prop="simple_normality", status="proved_not_simply_normal"),
            self.rec(radix="base 3", prop="full_normality", status="proved_nonnormal"),
        ]
        self.assertEqual([x for x in self.errors(c, f) if "BC-01" in x], [])


class ConsistencyFunctionTests(unittest.TestCase):
    def test_bench_radix_consistency(self):
        f = portal.bench_radix_consistency
        self.assertEqual(f({}), [])
        self.assertEqual(f({"full_normality": "proved_normal", "simple_normality": "proved_simply_normal",
                            "digit_frequency_status": "exact_law"}), [])
        self.assertTrue(f({"full_normality": "proved_normal", "digit_frequency_status": "nontrivial_bound"}))
        self.assertTrue(f({"discrepancy_status": "zero_normal"}))
        self.assertTrue(f({"discrepancy_status": "maximal_K_b"}))
        self.assertEqual(f({"discrepancy_status": "maximal_K_b", "full_normality": "proved_nonnormal"}), [])
        self.assertTrue(f({"simple_normality": "proved_simply_normal", "digit_frequency_status": "nontrivial_bound"}))
        # m6.2: mirror rule 7, exact_law needs a simple normality decision in the same radix.
        self.assertTrue(f({"digit_frequency_status": "exact_law"}))
        self.assertEqual(f({"digit_frequency_status": "exact_law", "simple_normality": "proved_not_simply_normal",
                            "full_normality": "proved_nonnormal"}), [])

    def test_years_and_identifiers(self):
        self.assertEqual(portal.bench_years("Stoneham 1973 and Bailey–Crandall 2002, 0.7996, base 10"), [1973, 2002])
        self.assertTrue(portal.bench_is_pre_program("Champernowne 1933"))
        self.assertFalse(portal.bench_is_pre_program("Captain Sude 2026, using 1729"))
        self.assertFalse(portal.bench_is_pre_program("no year"))
        self.assertEqual(portal.BENCH_ID_RE.findall("BF-07, BF-100 and BC-50"), ["BF-07", "BF-100", "BC-50"])

    def test_property_evidence(self):
        e = {"radices_scope": "base 2", "evidence": "lean+paper", "full_normality": "proved_nonnormal",
             "simple_normality": "open", "digit_frequency_status": "nontrivial_bound",
             "radix_results": [{"radix": "base 2", "property": "digit_frequency_status", "evidence": "paper"},
                               {"radix": "base 3", "property": "full_normality", "evidence": "external"}]}
        self.assertEqual(portal.bench_property_evidence(e, "digit_frequency_status"), "paper")
        self.assertEqual(portal.bench_property_evidence(e, "full_normality"), "lean+paper")
        self.assertEqual(portal.bench_property_evidence(e, "simple_normality"), "open")
        # A single-base bound without a scope record has no evidence (never the entry label).
        e["radix_results"] = []
        self.assertEqual(portal.bench_property_evidence(e, "digit_frequency_status"), "open")
        # All-bases scope and families: the entry-level label covers digit frequencies.
        e["radices_scope"] = "all integer bases b ≥ 2"
        self.assertEqual(portal.bench_property_evidence(e, "digit_frequency_status"), "lean+paper")
        fam = {k: v for k, v in e.items() if k != "radix_results"}
        fam["radices_scope"] = "construction radix b"
        self.assertEqual(portal.bench_property_evidence(fam, "digit_frequency_status"), "lean+paper")


class ProgressTableTests(BenchmarkCase):
    def test_sections_and_counts(self):
        c, f = self.data()
        text = portal.build_benchmarks_progress(c, f)
        for heading in ("## Summary by objective (50 fixed constants)",
                        "## Control constants and initially unresolved targets",
                        "## Counts by category", "## Classical constants (`BC-01` … `BC-50`)",
                        "## Per-radix and per-property results", "## Arithmetic families (`BF-01` …)"):
            self.assertIn(heading, text)
        self.assertLess(text.index("## Summary by objective"), text.index("## Control constants"))
        self.assertIn("| Control/reference / 8 | Initially unresolved / 42 |", text)
        n_records = sum(len(e["radix_results"]) for e in c["constant"])
        section = text.split("## Per-radix and per-property results", 1)[1].split("## Arithmetic families", 1)[0]
        self.assertEqual(sum(1 for line in section.splitlines() if line.startswith("| BC-")), n_records)

    def test_cohort_rows_partition(self):
        c, _ = self.data()
        for label, ctrl, unres, repo, ext in portal.bench_cohort_counts(c["constant"]):
            self.assertTrue(all(e["cohort"] == "control" for e in ctrl), label)
            self.assertTrue(all(e["cohort"] == "unresolved" for e in unres), label)
            repo_ids, ext_ids = {e["id"] for e in repo}, {e["id"] for e in ext}
            self.assertFalse(repo_ids & ext_ids, label)
            self.assertEqual(repo_ids | ext_ids, {e["id"] for e in unres}, label)

    def test_missing_evidence_is_never_credited_to_external_input(self):
        # M1: bypassing the schema check, an unbacked bound raises instead of counting as external.
        c, _ = self.data()
        e = self.const(c, "BC-01")
        e["digit_frequency_status"] = "nontrivial_bound"
        with self.assertRaisesRegex(ValueError, "BC-01: no evidence recorded for digit_frequency_status"):
            portal.bench_cohort_counts(c["constant"])
        c, _ = self.data()
        e = self.const(c, "BC-31")
        e["digit_frequency_status"] = "nontrivial_bound"
        with self.assertRaisesRegex(ValueError, "BC-31: no evidence recorded"):
            portal.bench_cohort_counts(c["constant"])

    def test_all_bases_bound_with_external_evidence_counts_as_external(self):
        c, _ = self.data()
        e = self.const(c, "BC-01")
        e.update(digit_frequency_status="nontrivial_bound", evidence="external")
        rows = {r[0]: r for r in portal.bench_cohort_counts(c["constant"])}
        _, _, unres, repo, ext = rows["Objective 3 (digit-frequency law or bound)"]
        self.assertIn("BC-01", [x["id"] for x in ext])
        self.assertNotIn("BC-01", [x["id"] for x in repo])

    def test_externally_decided_target_listed_separately(self):
        # m1: the cohort summary never credits an external decision to registry entries.
        c, f = self.data()
        e = self.const(c, "BC-43")
        e.update(full_normality="proved_nonnormal", simple_normality="proved_not_simply_normal",
                 digit_frequency_status="exact_law", evidence="external")
        self.assertEqual([x for x in self.errors(c, f) if "BC-43" in x], [])
        text = portal.build_benchmarks_progress(c, f)
        repo_row = next(x for x in text.splitlines() if x.startswith("| Unresolved: normality now decided")
                        and "by the repository" in x)
        ext_row = next(x for x in text.splitlines() if x.startswith("| Unresolved: normality now decided")
                       and "by external input" in x)
        self.assertNotIn("BC-43", repo_row)
        self.assertIn("BC-43", ext_row)
        text = portal.build_benchmarks_progress(*self.data())
        self.assertNotIn("by external input", text)

    def test_all_open_counts_include_digit_frequencies(self):
        # m5: a constant with only a digit-frequency bound is not counted as all open.
        def counts(c, f):
            text = portal.build_benchmarks_progress(c, f)
            summary = next(x for x in text.splitlines() if x.startswith("| All five distributional fields open |"))
            cat = next(x for x in text.splitlines() if x.startswith("| q-series, theta and modular values |"))
            return int(summary.split("|")[2]), int(cat.rstrip(" |").rsplit("|", 1)[1]), int(cat.split("|")[7])
        c, f = self.data()
        base_all, base_cat, base_df = counts(c, f)
        e = self.const(c, "BC-31")
        self.assertEqual(e["category"], "q_series_and_modular")
        e["digit_frequency_status"] = "nontrivial_bound"
        e["radix_results"] = [self.rec(source="Someone 1990: positive lower frequency of the digit 1")]
        self.assertEqual([x for x in self.errors(c, f) if "BC-31" in x], [])
        self.assertEqual(counts(c, f), (base_all - 1, base_cat - 1, base_df + 1))

    def test_external_only_target_is_credited_to_external_input(self):
        c, _ = self.data()
        e = self.const(c, "BC-01")
        e.update(full_normality="proved_nonnormal", simple_normality="proved_not_simply_normal",
                 digit_frequency_status="exact_law", evidence="external")
        rows = {label: (unres, repo, ext) for label, _, unres, repo, ext in portal.bench_cohort_counts(c["constant"])}
        unres, repo, ext = rows["Objective 2 (nonnormality)"]
        self.assertIn("BC-01", [x["id"] for x in unres])
        self.assertNotIn("BC-01", [x["id"] for x in repo])
        self.assertIn("BC-01", [x["id"] for x in ext])

    def test_digit_frequency_columns(self):
        c, f = self.data()
        text = portal.build_benchmarks_progress(c, f)
        row = next(line for line in text.splitlines() if line.startswith("| BC-29 |"))
        self.assertIn("| nontrivial bound |", row)
        self.assertIn("| unresolved |", row)
        frow = next(line for line in text.splitlines() if line.startswith("| BF-11 |"))
        self.assertIn("| exact law |", frow)


if __name__ == "__main__":
    unittest.main()
