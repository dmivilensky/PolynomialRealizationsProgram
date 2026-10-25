import chebyshev2.Certificates.Compact.AmplitudeBatches.Data015

/-!
Article: chebyshev2, Section 4.1.
Kernel reduction of acceptance for amplitude quadrature panels 480–511.
Use: `chebyshev2.Certificates.Compact.AmplitudeValues.check511` feeds
`chebyshev2.Certificates.Compact.AmplitudeValues.valid511` (valid511).
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
theorem check480 : AmplitudePolynomial.check scale ops epsilon panel480=true := by decide +kernel
theorem check481 : AmplitudePolynomial.check scale ops epsilon panel481=true := by decide +kernel
theorem check482 : AmplitudePolynomial.check scale ops epsilon panel482=true := by decide +kernel
theorem check483 : AmplitudePolynomial.check scale ops epsilon panel483=true := by decide +kernel
theorem check484 : AmplitudePolynomial.check scale ops epsilon panel484=true := by decide +kernel
theorem check485 : AmplitudePolynomial.check scale ops epsilon panel485=true := by decide +kernel
theorem check486 : AmplitudePolynomial.check scale ops epsilon panel486=true := by decide +kernel
theorem check487 : AmplitudePolynomial.check scale ops epsilon panel487=true := by decide +kernel
theorem check488 : AmplitudePolynomial.check scale ops epsilon panel488=true := by decide +kernel
theorem check489 : AmplitudePolynomial.check scale ops epsilon panel489=true := by decide +kernel
theorem check490 : AmplitudePolynomial.check scale ops epsilon panel490=true := by decide +kernel
theorem check491 : AmplitudePolynomial.check scale ops epsilon panel491=true := by decide +kernel
theorem check492 : AmplitudePolynomial.check scale ops epsilon panel492=true := by decide +kernel
theorem check493 : AmplitudePolynomial.check scale ops epsilon panel493=true := by decide +kernel
theorem check494 : AmplitudePolynomial.check scale ops epsilon panel494=true := by decide +kernel
theorem check495 : AmplitudePolynomial.check scale ops epsilon panel495=true := by decide +kernel
theorem check496 : AmplitudePolynomial.check scale ops epsilon panel496=true := by decide +kernel
theorem check497 : AmplitudePolynomial.check scale ops epsilon panel497=true := by decide +kernel
theorem check498 : AmplitudePolynomial.check scale ops epsilon panel498=true := by decide +kernel
theorem check499 : AmplitudePolynomial.check scale ops epsilon panel499=true := by decide +kernel
theorem check500 : AmplitudePolynomial.check scale ops epsilon panel500=true := by decide +kernel
theorem check501 : AmplitudePolynomial.check scale ops epsilon panel501=true := by decide +kernel
theorem check502 : AmplitudePolynomial.check scale ops epsilon panel502=true := by decide +kernel
theorem check503 : AmplitudePolynomial.check scale ops epsilon panel503=true := by decide +kernel
theorem check504 : AmplitudePolynomial.check scale ops epsilon panel504=true := by decide +kernel
theorem check505 : AmplitudePolynomial.check scale ops epsilon panel505=true := by decide +kernel
theorem check506 : AmplitudePolynomial.check scale ops epsilon panel506=true := by decide +kernel
theorem check507 : AmplitudePolynomial.check scale ops epsilon panel507=true := by decide +kernel
theorem check508 : AmplitudePolynomial.check scale ops epsilon panel508=true := by decide +kernel
theorem check509 : AmplitudePolynomial.check scale ops epsilon panel509=true := by decide +kernel
theorem check510 : AmplitudePolynomial.check scale ops epsilon panel510=true := by decide +kernel
theorem check511 : AmplitudePolynomial.check scale ops epsilon panel511=true := by decide +kernel
end chebyshev2.Certificates.Compact.AmplitudeValues
