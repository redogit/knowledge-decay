import importlib.util
from pathlib import Path
import sys
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'code'))

class TheoremTwoCrosscheckTests(unittest.TestCase):
    def test_exact_extremes_and_sharing_pairs(self):
        self.assertIsNotNone(importlib.util.find_spec('verify_theorem_two'))
        import verify_theorem_two as v
        for mask,want in [(0,(None,None,None)),(1<<8,(5,3,3)),
                          (1<<14,(2,2,2)),(1<<9,(1,1,1)),
                          ((1<<8)|1,(3,2,2)),((1<<1)|(1<<12),(3,3,3)),
                          ((1<<6)|(1<<12),(2,2,2)),(65535,(1,1,1))]:
            with self.subTest(mask=mask):
                self.assertEqual(v.minimum_costs(mask),want)
                self.assertEqual(v.expected_costs(v.classify(mask)),want)
        for bad in (-1,65536,True,'8'):
            with self.subTest(bad=bad),self.assertRaises(ValueError):
                v.minimum_costs(bad)

    def test_truth_table_orientation(self):
        self.assertIsNotNone(importlib.util.find_spec('verify_theorem_two'))
        import verify_theorem_two as v
        for op in range(16):
            got=''.join(str(v.scalar(op,a,b)) for a,b in [(0,0),(0,1),(1,0),(1,1)])
            self.assertEqual(got,f'{op:04b}')

if __name__=='__main__':
    unittest.main()
