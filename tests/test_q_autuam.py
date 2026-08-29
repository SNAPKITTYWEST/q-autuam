# Copyright (c) 2026 BEL ESPRIT D ACCORD TRUST HOLDINGS INC. All rights reserved.

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src', 'q_autuam'))

import unittest
from q_autuam import (
    parity, rec_trig, prime_factors, elucid,
    annotation_multiset, entropy, emergence, intent,
    horn_satisfy, solve_3sat_trunc_error, q_autuam_solve,
    TRUNC_ERROR_NUM, TRUNC_ERROR_DEN
)


class TestRecTrig(unittest.TestCase):
    def test_base_parity(self):
        bits = [1, 0, 1, 1]
        result = rec_trig(bits, 0)
        self.assertEqual(result, [parity(bits)] * len(bits))

    def test_boolean_output_all_depths(self):
        bits = [1, 0, 1, 1, 0]
        for k in range(6):
            out = rec_trig(bits, k)
            self.assertTrue(all(b in (0, 1) for b in out),
                            f"Non-boolean output at depth {k}")

    def test_depth_determinism(self):
        bits = [1, 1, 0, 0, 1]
        self.assertEqual(rec_trig(bits, 3), rec_trig(bits, 3))


class TestElucidian(unittest.TestCase):
    def test_prime_factors(self):
        self.assertEqual(prime_factors(12), {2: 2, 3: 1})
        self.assertEqual(prime_factors(1), {})
        self.assertEqual(prime_factors(7), {7: 1})

    def test_elucid_prime(self):
        self.assertEqual(elucid(7), ((7, 1),))

    def test_elucid_composite(self):
        self.assertEqual(elucid(12), ((2, 2), (3, 1)))


class TestEntropyEmergence(unittest.TestCase):
    def test_entropy_nonneg(self):
        annot = annotation_multiset([1, 0, 1, 0, 1])
        self.assertGreaterEqual(entropy(annot), 0.0)

    def test_emergence_nonneg(self):
        annot = annotation_multiset([1, 1, 1, 0, 1])
        self.assertGreaterEqual(emergence(annot), 0.0)

    def test_intent_in_unit_interval(self):
        bits = [1, 0, 1, 1, 0, 1]
        for k in range(4):
            score = intent(bits, k)
            self.assertGreaterEqual(score, 0.0)
            self.assertLessEqual(score, 1.0)


class TestSATCore(unittest.TestCase):
    def test_unsat_outside_family(self):
        # Random tiny formula — not in the 89/2462 family
        clauses = [[1, -2, 3], [-1, 2, -3], [2, 3, -4]]
        result = solve_3sat_trunc_error(clauses, n_vars=4)
        self.assertIsNone(result)

    def test_horn_satisfy_unit_clauses(self):
        # Force x1=1, x2=0, x3=1
        clauses = [[1], [-2], [3]]
        assignment = horn_satisfy(clauses, n_vars=3)
        self.assertIsNotNone(assignment)

    def test_q_autuam_solve_constructed_instance(self):
        # Build a formula with exactly 89 forced-false unit clauses
        # and remaining positive unit clauses (trivially Horn-sat)
        n = 200
        clauses = []
        for i in range(1, TRUNC_ERROR_NUM + 1):
            clauses.append([-i])   # force x_i = 0 (unsatisfied if we set x_i=1)
        for i in range(TRUNC_ERROR_NUM + 1, n + 1):
            clauses.append([i])    # positive unit — satisfied by x_i=1

        result = q_autuam_solve(clauses, n_vars=n, k_max=3)
        self.assertIsNotNone(result)
        self.assertGreaterEqual(result['intent'], 0.0)

    def test_intent_threshold_flag(self):
        n = 200
        clauses = []
        for i in range(1, TRUNC_ERROR_NUM + 1):
            clauses.append([-i])
        for i in range(TRUNC_ERROR_NUM + 1, n + 1):
            clauses.append([i])
        result = q_autuam_solve(clauses, n_vars=n, k_max=3, intent_threshold=0.0)
        self.assertIsNotNone(result)
        self.assertTrue(result['high_intent'])  # always true when threshold=0


class TestTruncErrorConstant(unittest.TestCase):
    def test_fraction_in_lowest_terms(self):
        from math import gcd
        self.assertEqual(gcd(TRUNC_ERROR_NUM, TRUNC_ERROR_DEN), 1)

    def test_values(self):
        self.assertEqual(TRUNC_ERROR_NUM, 89)
        self.assertEqual(TRUNC_ERROR_DEN, 2462)


if __name__ == '__main__':
    unittest.main()
