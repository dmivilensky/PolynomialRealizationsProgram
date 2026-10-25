import polyak.CertifiedExamples.Exact313.Code
import polyak.Numerics.KernelDecide
import Mathlib.Analysis.Real.Pi.Bounds

/-! Generated rational proposals for the exact 3/13 source equation. -/
namespace polyak.Certificates.PartII.Exact313
open LeanCert.Core LeanCert.Engine polyak.Numerics.Parametric

def piBox : IntervalRat :=
  ⟨314159265358979323846/100000000000000000000,
    314159265358979323847/100000000000000000000,by norm_num⟩

def certificate : WeightedCertificate 1 where
  center := ![(4263072232460995241336280913875253841501343/31250000000000000000000000000000000000000000)]
  radius := ![(1/1000000000000000)]
  preconditioner := !![(-53825382101441543316463467752246216428236209/250000000000000000000000000000000000000000000)]

def config : DyadicConfig := {precision:=-256,taylorDepth:=64}

theorem accepted : checkDyadic
    polyak.CertifiedExamples.Exact313.Code.equations piBox certificate config=true := by
  kernel_decide

end polyak.Certificates.PartII.Exact313
