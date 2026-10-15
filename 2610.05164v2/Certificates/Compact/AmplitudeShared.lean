import «2610.05164v2».Numerics.AmplitudeCheck
import «2610.05164v2».Certificates.Compact.ContactShared

/-!
Article: 2610.05164v2, Section 4.1.
Amplitude Shared.
Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.shapeQ` feeds
`«2610.05164v2».Certificates.Compact.AmplitudeValues.ValidPanel.actual` (actual).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace «2610.05164v2».Certificates.Compact.AmplitudeValues
open «2610.05164v2».Numerics «2610.05164v2».Numerics.IntegerCertificate
noncomputable def ops : List Op := [.mul 2 2,.mul 0 3,.literal (2) 1,.neg 1,.add 1 0,.mul 3 0,.literal (1) 4,.mul 10 10,.mul 1 0,.literal (676065451111757) 250000000000,.add 15 16,.mul 1 0,.add 9 0,.mul 7 2,.mul 19 20,.mul 12 0,.neg 0,.add 3 0,.mul 20 18,.mul 0 0,.mul 0 1,.mul 12 0,.literal (3) 1,.mul 17 4,.mul 1 0,.neg 0,.add 4 0,.literal (2771459803480839) 12500000000000000,.mul 0 22,.neg 0,.add 3 0,.mul 18 0,.literal (13513424903216799) 5000000000000,.mul 0 24,.mul 0 16,.neg 0,.add 4 0,.literal (6) 1,.mul 36 38,.mul 1 0,.neg 0,.add 42 0]
noncomputable def scale : Nat := ContactValues.scale
noncomputable def epsilon : ℚ := 1/10^10
theorem shapeK : codeExpressionCheck ops 33 AmplitudeExpr.k=true := by decide +kernel
theorem shapeD : codeExpressionCheck ops 29 (AmplitudeExpr.den DualInputs.sigma)=true := by decide +kernel
theorem shapeE : codeExpressionCheck ops 5 (AmplitudeExpr.rootResidual DualInputs.sigma DualInputs.base DualInputs.omega)=true := by decide +kernel
theorem shapeQ : codeExpressionCheck ops 0 AmplitudeExpr.quadratureResidual=true := by decide +kernel
end «2610.05164v2».Certificates.Compact.AmplitudeValues
