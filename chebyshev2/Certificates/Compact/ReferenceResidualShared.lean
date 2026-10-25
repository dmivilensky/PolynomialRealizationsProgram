import chebyshev2.Numerics.IntegerResidualCell
import chebyshev2.Certificates.DualInputs.ReferenceModel

/-!
Article: chebyshev2, Section 4.1.
Reference Residual Shared.
Use: `chebyshev2.Certificates.Compact.ReferenceResiduals.shapeODE` feeds
`chebyshev2.Certificates.Compact.ReferenceTrajectory.full_trajectory` (full trajectory).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace chebyshev2.Certificates.Compact.ReferenceResiduals
open chebyshev2.Numerics chebyshev2.Numerics.IntegerCertificate chebyshev2.Certificates.DualInputs
noncomputable def scale : Nat := 22300745198530623141535718272648361505980416
noncomputable def piBounds : Bounds := ⟨70059857285281660787732012935536363654390793,70059857285281660787732012935536363654390794⟩
noncomputable def ops : List Op := [.literal (2) 1,.mul 1 1,.mul 0 2,.neg 0,.add 3 0,.mul 2 0,.literal (1) 4,.mul 8 8,.mul 1 0,.literal (1) 1,.literal (2220923872881923) 20000000000000000,.literal (546732465760943) 2000000000000000000,.add 6 0,.mul 2 0,.literal (4567720140479483) 125000000000000000,.mul 9 5,.mul 1 0,.add 3 0,.mul 8 5,.literal (2305100467697839) 1000000000000000000,.add 14 0,.mul 3 0,.literal (2725840545911301) 10000000000000000,.mul 17 4,.mul 1 0,.add 3 0,.mul 7 5,.literal (767733003061487) 62500000000000000,.add 22 0,.mul 3 0,.literal (1691609045019719) 2500000000000000,.mul 25 4,.mul 1 0,.add 3 0,.mul 7 5,.literal (31106138506646317) 500000000000000000,.add 30 0,.mul 3 0,.literal (7982060966163923) 50000000000000000,.mul 33 4,.mul 1 0,.add 3 0,.mul 7 5,.literal (5577071733518729) 10000000000000000,.add 38 0,.mul 3 0,.literal (6784196413046893) 100000000000000000,.mul 41 4,.mul 1 0,.add 3 0,.mul 7 5,.mul 53 53,.mul 0 54,.mul 44 0,.literal (3) 1,.mul 55 50,.mul 0 58,.mul 2 0,.neg 0,.add 5 0,.mul 0 9,.mul 56 11,.mul 61 0,.neg 0,.add 3 0,.mul 10 63,.neg 70,.add 1 0,.mul 59 0,.mul 0 17,.mul 74 14,.add 1 0,.literal (6) 1,.mul 0 76,.neg 0,.add 3 0,.literal (2028196353335271) 250000000000,.mul 80 80,.mul 1 0,.neg 0,.add 4 0]
noncomputable def eta : ℚ := 1/10^14
theorem pi_mem : piBounds.Mem scale Real.pi :=
  rationalIntervalCheck_sound (by decide +kernel)
    (a := piHigh.lo) (b := piHigh.hi) (by decide +kernel) mem_piHigh.1 mem_piHigh.2
theorem shapeK : codeExpressionCheck ops 72 ResidualExpr.k=true := by decide +kernel
theorem shapeD : codeExpressionCheck ops 30 (ResidualExpr.profileParts reference).1=true := by decide +kernel
theorem shapeRoot : codeExpressionCheck ops 16 (ResidualExpr.rootResidual reference)=true := by decide +kernel
theorem shapeFactor : codeExpressionCheck ops 12 ResidualExpr.factor=true := by decide +kernel
theorem shapeODE : codeExpressionCheck ops 0 (ResidualExpr.odeResidual sigma)=true := by decide +kernel
end chebyshev2.Certificates.Compact.ReferenceResiduals
