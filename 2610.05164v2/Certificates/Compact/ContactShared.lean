import «2610.05164v2».Numerics.ContactModelSound
import «2610.05164v2».Numerics.ValueQuadrature
import «2610.05164v2».Certificates.Compact.ReferenceResidualShared

/-!
Article: 2610.05164v2, Section 4.1.
Contact Shared.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.shapeE` feeds
`«2610.05164v2».Certificates.Compact.ContactValues.ValidPanel.actual` (actual).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace «2610.05164v2».Certificates.Compact.ContactValues
open «2610.05164v2».Numerics «2610.05164v2».Numerics.IntegerCertificate
noncomputable def scale : Nat := ReferenceResiduals.scale
noncomputable def piBounds : Bounds := ReferenceResiduals.piBounds
noncomputable def epsilon : ℚ := 1/10^12
noncomputable def leftRadius : Int := 446014903970612462830714365453
noncomputable def rightRadius : Int := 892029807941224925661428730906
noncomputable def ops : List Op := [.mul 0 0,.mul 0 1,.literal (2) 1,.neg 1,.add 1 0,.mul 3 0,.literal (676065451111757) 250000000000,.add 10 11,.mul 1 0,.add 6 0,.literal (1) 4,.mul 12 12,.mul 1 0,.mul 15 15,.mul 1 0,.mul 15 10,.neg 0,.add 2 0,.mul 12 10,.mul 22 23,.mul 17 0,.neg 0,.add 3 0,.literal (3) 1,.mul 21 1,.mul 28 28,.mul 30 30,.add 1 0,.mul 0 18,.neg 0,.add 5 0,.mul 7 0,.mul 22 14,.mul 38 0,.neg 0,.add 3 0]
theorem shapeD : codeExpressionCheck ops 26 (ContactExpr.gammaDen DualInputs.sigma)=true := by decide +kernel
theorem shapeV : codeExpressionCheck ops 18 ContactExpr.speed=true := by decide +kernel
theorem shapeE : codeExpressionCheck ops 0 (ContactExpr.residual DualInputs.sigma)=true := by decide +kernel
end «2610.05164v2».Certificates.Compact.ContactValues
