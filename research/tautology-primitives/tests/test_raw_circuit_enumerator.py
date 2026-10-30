import importlib.util
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'code'))


class RawEnumeratorTests(unittest.TestCase):
    def test_independent_ordered_syntax_enumeration(self):
        self.assertIsNotNone(importlib.util.find_spec('raw_circuit_enumerator'))
        import raw_circuit_enumerator as raw
        nor = raw.enumerate_basis((8,))
        self.assertEqual(nor['minimum'], {'formula_gates': 5, 'dag_gates': 3, 'depth': 3})
        self.assertEqual([x['programs'] for x in nor['dag_layers']], [1, 1, 4, 36])
        self.assertEqual([x['trees'] for x in nor['formula_layers']], [1, 1, 2, 5, 14, 42])
        self.assertEqual([x['true_trees'] for x in nor['formula_layers'][:5]], [0]*5)

    def test_source_orientation_and_mixed_basis(self):
        self.assertIsNotNone(importlib.util.find_spec('raw_circuit_enumerator'))
        import raw_circuit_enumerator as raw
        for op in range(16):
            for a, b in ((0, 0), (0, 1), (1, 0), (1, 1)):
                self.assertEqual(raw.scalar(op, a, b), int(f'{op:04b}'[2*a+b]))
        self.assertEqual(raw.enumerate_basis((0, 8))['minimum'],
                         {'formula_gates': 3, 'dag_gates': 2, 'depth': 2})


if __name__ == '__main__':
    unittest.main()
