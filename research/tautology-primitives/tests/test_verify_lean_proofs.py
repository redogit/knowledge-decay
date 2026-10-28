import importlib.util
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'code'))


class LeanVerificationPolicyTests(unittest.TestCase):
    def test_extra_axioms_and_placeholders_cannot_pass_the_audit(self):
        self.assertIsNotNone(importlib.util.find_spec('verify_lean_proofs'))
        import verify_lean_proofs as verify
        self.assertEqual(verify.axioms_from_output(
            "'FIG22.Tree.singleton_minima' depends on axioms: [propext, Quot.sound]\n"),
            {'propext', 'Quot.sound'})
        for forbidden in ('sorryAx', 'researchAssumption', 'Lean.ofReduceBool'):
            with self.subTest(forbidden=forbidden), self.assertRaises(RuntimeError):
                verify.axioms_from_output(f"'claim' depends on axioms: [{forbidden}]\n")
        with self.assertRaises(RuntimeError):
            verify.check_source('theorem unfinished : True := by sorry')
        with self.assertRaises(RuntimeError):
            verify.check_source('axiom unsupported : False')
        with self.assertRaises(RuntimeError):
            verify.check_source('theorem t : True := by native_decide')
        verify.check_source('/- A comment about sorry, nested /- axiom -/ is not code. -/\ntheorem t : True := by trivial')



class LeanNegativeControlTests(unittest.TestCase):
    def test_rejection_must_be_for_a_false_proposition(self):
        import subprocess
        import verify_lean_proofs as verify
        self.assertTrue(hasattr(verify,'require_false_rejection'))
        verify.require_false_rejection(subprocess.CompletedProcess([],1,
            'error: Tactic `decide` proved that the proposition\n False\nis false\n'), 'false_claim')
        for status,output in [(0,''),(1,'error: unknown module TheoremTwoRaw'),(1,'timeout')]:
            with self.subTest(status=status,output=output),self.assertRaises(RuntimeError):
                verify.require_false_rejection(subprocess.CompletedProcess([],status,output),'false_claim')

if __name__ == '__main__':
    unittest.main()
