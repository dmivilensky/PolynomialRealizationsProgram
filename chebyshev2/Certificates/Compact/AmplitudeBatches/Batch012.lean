import chebyshev2.Certificates.Compact.AmplitudeBatches.Data012

/-!
Article: chebyshev2, Section 4.1.
Kernel reduction of acceptance for amplitude quadrature panels 384–415.
Use: `chebyshev2.Certificates.Compact.AmplitudeValues.check415` feeds
`chebyshev2.Certificates.Compact.AmplitudeValues.valid415` (valid415).
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
theorem check384 : AmplitudePolynomial.check scale ops epsilon panel384=true := by decide +kernel
theorem check385 : AmplitudePolynomial.check scale ops epsilon panel385=true := by decide +kernel
theorem check386 : AmplitudePolynomial.check scale ops epsilon panel386=true := by decide +kernel
theorem check387 : AmplitudePolynomial.check scale ops epsilon panel387=true := by decide +kernel
theorem check388 : AmplitudePolynomial.check scale ops epsilon panel388=true := by decide +kernel
theorem check389 : AmplitudePolynomial.check scale ops epsilon panel389=true := by decide +kernel
theorem check390 : AmplitudePolynomial.check scale ops epsilon panel390=true := by decide +kernel
theorem check391 : AmplitudePolynomial.check scale ops epsilon panel391=true := by decide +kernel
theorem check392 : AmplitudePolynomial.check scale ops epsilon panel392=true := by decide +kernel
theorem check393 : AmplitudePolynomial.check scale ops epsilon panel393=true := by decide +kernel
theorem check394 : AmplitudePolynomial.check scale ops epsilon panel394=true := by decide +kernel
theorem check395 : AmplitudePolynomial.check scale ops epsilon panel395=true := by decide +kernel
theorem check396 : AmplitudePolynomial.check scale ops epsilon panel396=true := by decide +kernel
theorem check397 : AmplitudePolynomial.check scale ops epsilon panel397=true := by decide +kernel
theorem check398 : AmplitudePolynomial.check scale ops epsilon panel398=true := by decide +kernel
theorem check399 : AmplitudePolynomial.check scale ops epsilon panel399=true := by decide +kernel
theorem check400 : AmplitudePolynomial.check scale ops epsilon panel400=true := by decide +kernel
theorem check401 : AmplitudePolynomial.check scale ops epsilon panel401=true := by decide +kernel
theorem check402 : AmplitudePolynomial.check scale ops epsilon panel402=true := by decide +kernel
theorem check403 : AmplitudePolynomial.check scale ops epsilon panel403=true := by decide +kernel
theorem check404 : AmplitudePolynomial.check scale ops epsilon panel404=true := by decide +kernel
theorem check405 : AmplitudePolynomial.check scale ops epsilon panel405=true := by decide +kernel
theorem check406 : AmplitudePolynomial.check scale ops epsilon panel406=true := by decide +kernel
theorem check407 : AmplitudePolynomial.check scale ops epsilon panel407=true := by decide +kernel
theorem check408 : AmplitudePolynomial.check scale ops epsilon panel408=true := by decide +kernel
theorem check409 : AmplitudePolynomial.check scale ops epsilon panel409=true := by decide +kernel
theorem check410 : AmplitudePolynomial.check scale ops epsilon panel410=true := by decide +kernel
theorem check411 : AmplitudePolynomial.check scale ops epsilon panel411=true := by decide +kernel
theorem check412 : AmplitudePolynomial.check scale ops epsilon panel412=true := by decide +kernel
theorem check413 : AmplitudePolynomial.check scale ops epsilon panel413=true := by decide +kernel
theorem check414 : AmplitudePolynomial.check scale ops epsilon panel414=true := by decide +kernel
theorem check415 : AmplitudePolynomial.check scale ops epsilon panel415=true := by decide +kernel
end chebyshev2.Certificates.Compact.AmplitudeValues
