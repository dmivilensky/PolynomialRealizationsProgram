import «2610.05164v2».Certificates.Compact.ContactBatches.Data022

/-!
Article: 2610.05164v2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 704–735.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.residualCheck735` feeds
`«2610.05164v2».Certificates.Compact.ContactValues.valid735` (valid735).
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
theorem modelCheck704 : panel704.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck704 : ContactPolynomial.check scale ops epsilon panel704.row=true := by decide +kernel
theorem modelCheck705 : panel705.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck705 : ContactPolynomial.check scale ops epsilon panel705.row=true := by decide +kernel
theorem modelCheck706 : panel706.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck706 : ContactPolynomial.check scale ops epsilon panel706.row=true := by decide +kernel
theorem modelCheck707 : panel707.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck707 : ContactPolynomial.check scale ops epsilon panel707.row=true := by decide +kernel
theorem modelCheck708 : panel708.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck708 : ContactPolynomial.check scale ops epsilon panel708.row=true := by decide +kernel
theorem modelCheck709 : panel709.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck709 : ContactPolynomial.check scale ops epsilon panel709.row=true := by decide +kernel
theorem modelCheck710 : panel710.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck710 : ContactPolynomial.check scale ops epsilon panel710.row=true := by decide +kernel
theorem modelCheck711 : panel711.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck711 : ContactPolynomial.check scale ops epsilon panel711.row=true := by decide +kernel
theorem modelCheck712 : panel712.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck712 : ContactPolynomial.check scale ops epsilon panel712.row=true := by decide +kernel
theorem modelCheck713 : panel713.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck713 : ContactPolynomial.check scale ops epsilon panel713.row=true := by decide +kernel
theorem modelCheck714 : panel714.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck714 : ContactPolynomial.check scale ops epsilon panel714.row=true := by decide +kernel
theorem modelCheck715 : panel715.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck715 : ContactPolynomial.check scale ops epsilon panel715.row=true := by decide +kernel
theorem modelCheck716 : panel716.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck716 : ContactPolynomial.check scale ops epsilon panel716.row=true := by decide +kernel
theorem modelCheck717 : panel717.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck717 : ContactPolynomial.check scale ops epsilon panel717.row=true := by decide +kernel
theorem modelCheck718 : panel718.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck718 : ContactPolynomial.check scale ops epsilon panel718.row=true := by decide +kernel
theorem modelCheck719 : panel719.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck719 : ContactPolynomial.check scale ops epsilon panel719.row=true := by decide +kernel
theorem modelCheck720 : panel720.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck720 : ContactPolynomial.check scale ops epsilon panel720.row=true := by decide +kernel
theorem modelCheck721 : panel721.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck721 : ContactPolynomial.check scale ops epsilon panel721.row=true := by decide +kernel
theorem modelCheck722 : panel722.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck722 : ContactPolynomial.check scale ops epsilon panel722.row=true := by decide +kernel
theorem modelCheck723 : panel723.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck723 : ContactPolynomial.check scale ops epsilon panel723.row=true := by decide +kernel
theorem modelCheck724 : panel724.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck724 : ContactPolynomial.check scale ops epsilon panel724.row=true := by decide +kernel
theorem modelCheck725 : panel725.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck725 : ContactPolynomial.check scale ops epsilon panel725.row=true := by decide +kernel
theorem modelCheck726 : panel726.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck726 : ContactPolynomial.check scale ops epsilon panel726.row=true := by decide +kernel
theorem modelCheck727 : panel727.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck727 : ContactPolynomial.check scale ops epsilon panel727.row=true := by decide +kernel
theorem modelCheck728 : panel728.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck728 : ContactPolynomial.check scale ops epsilon panel728.row=true := by decide +kernel
theorem modelCheck729 : panel729.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck729 : ContactPolynomial.check scale ops epsilon panel729.row=true := by decide +kernel
theorem modelCheck730 : panel730.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck730 : ContactPolynomial.check scale ops epsilon panel730.row=true := by decide +kernel
theorem modelCheck731 : panel731.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck731 : ContactPolynomial.check scale ops epsilon panel731.row=true := by decide +kernel
theorem modelCheck732 : panel732.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck732 : ContactPolynomial.check scale ops epsilon panel732.row=true := by decide +kernel
theorem modelCheck733 : panel733.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck733 : ContactPolynomial.check scale ops epsilon panel733.row=true := by decide +kernel
theorem modelCheck734 : panel734.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck734 : ContactPolynomial.check scale ops epsilon panel734.row=true := by decide +kernel
theorem modelCheck735 : panel735.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck735 : ContactPolynomial.check scale ops epsilon panel735.row=true := by decide +kernel
end «2610.05164v2».Certificates.Compact.ContactValues
