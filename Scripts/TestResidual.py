"""Adversarial checks of bounded-degree models and their checkpoints."""
import subprocess
import tempfile
import unittest
from pathlib import Path
from FetchCertificate import ROOT


class ResidualTests(unittest.TestCase):
    """
    Adversarial kernel tests of polynomial residual acceptance, including a forged truncation
    claim.
    """
    def test_kernel_boundaries(self):
        """
        Ask Lean to accept valid checker examples and reject a false tail/truncation assertion.
        This tests the acceptance boundary rather than a Python success report.
        """
        source='''import «2610.05164v2».Numerics.IntegerResidualCell
set_option autoImplicit false
open «2610.05164v2».Numerics.IntegerCertificate
open Poly
example : truncate 100 1 [⟨0,0⟩,⟨100,100⟩]=some [⟨0,100⟩] := by decide +kernel
example : truncate 100 1 [⟨0,0⟩,⟨-100,-100⟩]=some [⟨-100,0⟩] := by decide +kernel
example : truncate 100 1 [⟨0,0⟩,⟨100,100⟩]≠some [⟨0,0⟩] := by decide +kernel
example : truncate 100 0 [⟨100,100⟩]=some [⟨0,100⟩] := by decide +kernel
example : Taylor.checkpoint [⟨1,2⟩] (some [⟨1,3⟩])=none := by decide +kernel
example : Taylor.checkpoint [⟨1,2⟩] (some [⟨1,2⟩])=some [⟨1,2⟩] := by decide +kernel
example : Taylor.evalProgram 100 2 [] [] [.literal 1 1]=none := by decide +kernel
example : Taylor.evalProgram 100 2 [] [none] []=none := by decide +kernel
example : Taylor.evalProgram 100 2 [] [some [⟨0,0⟩]] [.literal 1 1]=none := by decide +kernel
example : Taylor.evalProgram 100 2 [] [none] [.copy 0]=none := by decide +kernel
example : Taylor.evalProgram 100 2 [] [none] [.inv 0]=none := by decide +kernel
example : Taylor.evalProgram 100 2 [] [none] [.cubic 0 0]=none := by decide +kernel
'''
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'ResidualBoundaries.lean';path.write_text(source)
            result=subprocess.run(['lake','env','lean',str(path)],cwd=ROOT,capture_output=True,text=True,timeout=90)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            path.write_text(source+'\nexample : truncate 100 1 [⟨0,0⟩,⟨100,100⟩]=some [⟨0,0⟩] := by decide +kernel\n')
            result=subprocess.run(['lake','env','lean',str(path)],cwd=ROOT,capture_output=True,text=True,timeout=90)
            self.assertNotEqual(result.returncode,0,'Forged tail bound accepted')


if __name__=='__main__':unittest.main()
