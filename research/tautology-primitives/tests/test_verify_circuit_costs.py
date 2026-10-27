import importlib.util
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'code'))


class CrossVerificationTests(unittest.TestCase):
    def test_every_small_basis_and_concrete_witness_is_cross_checked(self):
        self.assertIsNotNone(importlib.util.find_spec('verify_circuit_costs'))
        import verify_circuit_costs as verify
        optimized, raw = verify.build_evidence()
        self.assertEqual(optimized['bases_checked'], 136)
        self.assertEqual(optimized['generates_true'], 93)
        self.assertEqual(optimized['does_not_generate_true'], 43)
        self.assertEqual(optimized['raw_trees_checked'], 195320)
        self.assertEqual(optimized['raw_programs_checked'], 37512)
        self.assertEqual(optimized['histogram_formula_dag_depth'], raw['histogram_formula_dag_depth'])
        self.assertEqual(optimized['witnesses_checked'], 279)


if __name__ == '__main__':
    unittest.main()
