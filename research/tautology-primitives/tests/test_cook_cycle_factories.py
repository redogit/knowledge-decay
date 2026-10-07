import unittest
from itertools import combinations
from pathlib import Path
import sys

PROJECT_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PROJECT_ROOT / "code"))

import cook_cycle_factories as m


class CycleFactoryTests(unittest.TestCase):
    def test_anchor(self):
        anchor = (4 << 41) | (120 << 25) | (8 << 16) | (2 << 12) | (3 << 7) | 15
        result = m.Factories.cook_cycle(anchor).run()
        self.assertTrue(result.ok)
        self.assertEqual(result.states.s3, 8800120086943)
        self.assertEqual(result.states.final_word, 31)

    def test_tautology_singletons(self):
        got = [
            op.name
            for op in m.BooleanOperatorFactory.all()
            if m.Factories.tautology().operator(op).run().generates_true
        ]
        self.assertEqual(
            got,
            ['NOR', 'XNOR', 'Y_IMPLIES_X', 'X_IMPLIES_Y', 'NAND', 'TRUE'],
        )

    def test_two_obstruction_theorem_for_all_singletons_and_pairs(self):
        ops = m.BooleanOperatorFactory.all()
        checked = 0
        for size in (1, 2):
            for basis in combinations(ops, size):
                actual = m.Factories.tautology().operators(basis).run().generates_true
                expected = (
                    not all(op.preserves_zero for op in basis)
                    and not all(op.self_dual for op in basis)
                )
                self.assertEqual(actual, expected, [op.name for op in basis])
                checked += 1
        self.assertEqual(checked, 136)


if __name__ == '__main__':
    unittest.main()
