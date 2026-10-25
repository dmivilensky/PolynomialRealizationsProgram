import chebyshev2.Certificates.Compact.AmplitudeBatches.Data025

/-!
Article: chebyshev2, Section 4.1.
Kernel reduction of acceptance for amplitude quadrature panels 800–831.
Use: `chebyshev2.Certificates.Compact.AmplitudeValues.check831` feeds
`chebyshev2.Certificates.Compact.AmplitudeValues.valid831` (valid831).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace chebyshev2.Certificates.Compact.AmplitudeValues
open chebyshev2.Numerics chebyshev2.Numerics.IntegerCertificate
theorem check800 : AmplitudePolynomial.check scale ops epsilon panel800=true := by decide +kernel
theorem check801 : AmplitudePolynomial.check scale ops epsilon panel801=true := by decide +kernel
theorem check802 : AmplitudePolynomial.check scale ops epsilon panel802=true := by decide +kernel
theorem check803 : AmplitudePolynomial.check scale ops epsilon panel803=true := by decide +kernel
theorem check804 : AmplitudePolynomial.check scale ops epsilon panel804=true := by decide +kernel
theorem check805 : AmplitudePolynomial.check scale ops epsilon panel805=true := by decide +kernel
theorem check806 : AmplitudePolynomial.check scale ops epsilon panel806=true := by decide +kernel
theorem check807 : AmplitudePolynomial.check scale ops epsilon panel807=true := by decide +kernel
theorem check808 : AmplitudePolynomial.check scale ops epsilon panel808=true := by decide +kernel
theorem check809 : AmplitudePolynomial.check scale ops epsilon panel809=true := by decide +kernel
theorem check810 : AmplitudePolynomial.check scale ops epsilon panel810=true := by decide +kernel
theorem check811 : AmplitudePolynomial.check scale ops epsilon panel811=true := by decide +kernel
theorem check812 : AmplitudePolynomial.check scale ops epsilon panel812=true := by decide +kernel
theorem check813 : AmplitudePolynomial.check scale ops epsilon panel813=true := by decide +kernel
theorem check814 : AmplitudePolynomial.check scale ops epsilon panel814=true := by decide +kernel
theorem check815 : AmplitudePolynomial.check scale ops epsilon panel815=true := by decide +kernel
theorem check816 : AmplitudePolynomial.check scale ops epsilon panel816=true := by decide +kernel
theorem check817 : AmplitudePolynomial.check scale ops epsilon panel817=true := by decide +kernel
theorem check818 : AmplitudePolynomial.check scale ops epsilon panel818=true := by decide +kernel
theorem check819 : AmplitudePolynomial.check scale ops epsilon panel819=true := by decide +kernel
theorem check820 : AmplitudePolynomial.check scale ops epsilon panel820=true := by decide +kernel
theorem check821 : AmplitudePolynomial.check scale ops epsilon panel821=true := by decide +kernel
theorem check822 : AmplitudePolynomial.check scale ops epsilon panel822=true := by decide +kernel
theorem check823 : AmplitudePolynomial.check scale ops epsilon panel823=true := by decide +kernel
theorem check824 : AmplitudePolynomial.check scale ops epsilon panel824=true := by decide +kernel
theorem check825 : AmplitudePolynomial.check scale ops epsilon panel825=true := by decide +kernel
theorem check826 : AmplitudePolynomial.check scale ops epsilon panel826=true := by decide +kernel
theorem check827 : AmplitudePolynomial.check scale ops epsilon panel827=true := by decide +kernel
theorem check828 : AmplitudePolynomial.check scale ops epsilon panel828=true := by decide +kernel
theorem check829 : AmplitudePolynomial.check scale ops epsilon panel829=true := by decide +kernel
theorem check830 : AmplitudePolynomial.check scale ops epsilon panel830=true := by decide +kernel
theorem check831 : AmplitudePolynomial.check scale ops epsilon panel831=true := by decide +kernel
end chebyshev2.Certificates.Compact.AmplitudeValues
