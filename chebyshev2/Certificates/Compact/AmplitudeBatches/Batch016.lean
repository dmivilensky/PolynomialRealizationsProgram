import chebyshev2.Certificates.Compact.AmplitudeBatches.Data016

/-!
Article: chebyshev2, Section 4.1.
Kernel reduction of acceptance for amplitude quadrature panels 512–543.
Use: `chebyshev2.Certificates.Compact.AmplitudeValues.check543` feeds
`chebyshev2.Certificates.Compact.AmplitudeValues.valid543` (valid543).
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
theorem check512 : AmplitudePolynomial.check scale ops epsilon panel512=true := by decide +kernel
theorem check513 : AmplitudePolynomial.check scale ops epsilon panel513=true := by decide +kernel
theorem check514 : AmplitudePolynomial.check scale ops epsilon panel514=true := by decide +kernel
theorem check515 : AmplitudePolynomial.check scale ops epsilon panel515=true := by decide +kernel
theorem check516 : AmplitudePolynomial.check scale ops epsilon panel516=true := by decide +kernel
theorem check517 : AmplitudePolynomial.check scale ops epsilon panel517=true := by decide +kernel
theorem check518 : AmplitudePolynomial.check scale ops epsilon panel518=true := by decide +kernel
theorem check519 : AmplitudePolynomial.check scale ops epsilon panel519=true := by decide +kernel
theorem check520 : AmplitudePolynomial.check scale ops epsilon panel520=true := by decide +kernel
theorem check521 : AmplitudePolynomial.check scale ops epsilon panel521=true := by decide +kernel
theorem check522 : AmplitudePolynomial.check scale ops epsilon panel522=true := by decide +kernel
theorem check523 : AmplitudePolynomial.check scale ops epsilon panel523=true := by decide +kernel
theorem check524 : AmplitudePolynomial.check scale ops epsilon panel524=true := by decide +kernel
theorem check525 : AmplitudePolynomial.check scale ops epsilon panel525=true := by decide +kernel
theorem check526 : AmplitudePolynomial.check scale ops epsilon panel526=true := by decide +kernel
theorem check527 : AmplitudePolynomial.check scale ops epsilon panel527=true := by decide +kernel
theorem check528 : AmplitudePolynomial.check scale ops epsilon panel528=true := by decide +kernel
theorem check529 : AmplitudePolynomial.check scale ops epsilon panel529=true := by decide +kernel
theorem check530 : AmplitudePolynomial.check scale ops epsilon panel530=true := by decide +kernel
theorem check531 : AmplitudePolynomial.check scale ops epsilon panel531=true := by decide +kernel
theorem check532 : AmplitudePolynomial.check scale ops epsilon panel532=true := by decide +kernel
theorem check533 : AmplitudePolynomial.check scale ops epsilon panel533=true := by decide +kernel
theorem check534 : AmplitudePolynomial.check scale ops epsilon panel534=true := by decide +kernel
theorem check535 : AmplitudePolynomial.check scale ops epsilon panel535=true := by decide +kernel
theorem check536 : AmplitudePolynomial.check scale ops epsilon panel536=true := by decide +kernel
theorem check537 : AmplitudePolynomial.check scale ops epsilon panel537=true := by decide +kernel
theorem check538 : AmplitudePolynomial.check scale ops epsilon panel538=true := by decide +kernel
theorem check539 : AmplitudePolynomial.check scale ops epsilon panel539=true := by decide +kernel
theorem check540 : AmplitudePolynomial.check scale ops epsilon panel540=true := by decide +kernel
theorem check541 : AmplitudePolynomial.check scale ops epsilon panel541=true := by decide +kernel
theorem check542 : AmplitudePolynomial.check scale ops epsilon panel542=true := by decide +kernel
theorem check543 : AmplitudePolynomial.check scale ops epsilon panel543=true := by decide +kernel
end chebyshev2.Certificates.Compact.AmplitudeValues
