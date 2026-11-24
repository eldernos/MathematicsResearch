import unittest

from strided_logarithm import (
    finite_certificates, golden_modulus_hits, low_transition_sieve, pi_hex_transitions, relations, validate,
)


class StridedLogarithmTests(unittest.TestCase):
    def test_exact_numerator_congruences(self):
        validate()

    def test_bounded_identity_search(self):
        found = relations()
        self.assertEqual([m for m, _ in found].count(1), 7)
        self.assertEqual([m for m, _ in found].count(2), 1)
        self.assertEqual(len(found), 8)

    def test_low_transition_sieve(self):
        self.assertEqual(low_transition_sieve(64, 12), (33, 24))
        self.assertEqual([low_transition_sieve(n, n) for n in (64, 128, 256, 512, 1024)],
                         [(33, 0), (43, 0), (64, 0), (97, 0), (134, 0)])

    def test_finite_orbit_certificates(self):
        self.assertEqual(finite_certificates(1024),
                         [(1, 650, 888), (2, 650, 888), (3, 641, 888), (5, 626, 864)])
        self.assertEqual(golden_modulus_hits(1024), (743, 327))
        self.assertEqual(pi_hex_transitions(128, 128), 66)
