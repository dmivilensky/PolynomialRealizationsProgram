import chebyshev2.Certificates.Compact.AmplitudeBatches.Data003

/-!
Article: chebyshev2, Section 4.1.
Kernel reduction of acceptance for amplitude quadrature panels 96–127.
Use: `chebyshev2.Certificates.Compact.AmplitudeValues.check127` feeds
`chebyshev2.Certificates.Compact.AmplitudeValues.valid127` (valid127).
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
theorem check96 : AmplitudePolynomial.check scale ops epsilon panel96=true := by decide +kernel
theorem check97 : AmplitudePolynomial.check scale ops epsilon panel97=true := by decide +kernel
theorem check98 : AmplitudePolynomial.check scale ops epsilon panel98=true := by decide +kernel
theorem check99 : AmplitudePolynomial.check scale ops epsilon panel99=true := by decide +kernel
theorem check100 : AmplitudePolynomial.check scale ops epsilon panel100=true := by decide +kernel
theorem check101 : AmplitudePolynomial.check scale ops epsilon panel101=true := by decide +kernel
theorem check102 : AmplitudePolynomial.check scale ops epsilon panel102=true := by decide +kernel
theorem check103 : AmplitudePolynomial.check scale ops epsilon panel103=true := by decide +kernel
theorem check104 : AmplitudePolynomial.check scale ops epsilon panel104=true := by decide +kernel
theorem check105 : AmplitudePolynomial.check scale ops epsilon panel105=true := by decide +kernel
theorem check106 : AmplitudePolynomial.check scale ops epsilon panel106=true := by decide +kernel
theorem check107 : AmplitudePolynomial.check scale ops epsilon panel107=true := by decide +kernel
theorem check108 : AmplitudePolynomial.check scale ops epsilon panel108=true := by decide +kernel
theorem check109 : AmplitudePolynomial.check scale ops epsilon panel109=true := by decide +kernel
theorem check110 : AmplitudePolynomial.check scale ops epsilon panel110=true := by decide +kernel
theorem check111 : AmplitudePolynomial.check scale ops epsilon panel111=true := by decide +kernel
theorem check112 : AmplitudePolynomial.check scale ops epsilon panel112=true := by decide +kernel
theorem check113 : AmplitudePolynomial.check scale ops epsilon panel113=true := by decide +kernel
theorem check114 : AmplitudePolynomial.check scale ops epsilon panel114=true := by decide +kernel
theorem check115 : AmplitudePolynomial.check scale ops epsilon panel115=true := by decide +kernel
theorem check116 : AmplitudePolynomial.check scale ops epsilon panel116=true := by decide +kernel
theorem check117 : AmplitudePolynomial.check scale ops epsilon panel117=true := by decide +kernel
theorem check118 : AmplitudePolynomial.check scale ops epsilon panel118=true := by decide +kernel
theorem check119 : AmplitudePolynomial.check scale ops epsilon panel119=true := by decide +kernel
theorem check120 : AmplitudePolynomial.check scale ops epsilon panel120=true := by decide +kernel
theorem check121 : AmplitudePolynomial.check scale ops epsilon panel121=true := by decide +kernel
theorem check122 : AmplitudePolynomial.check scale ops epsilon panel122=true := by decide +kernel
theorem check123 : AmplitudePolynomial.check scale ops epsilon panel123=true := by decide +kernel
theorem check124 : AmplitudePolynomial.check scale ops epsilon panel124=true := by decide +kernel
theorem check125 : AmplitudePolynomial.check scale ops epsilon panel125=true := by decide +kernel
theorem check126 : AmplitudePolynomial.check scale ops epsilon panel126=true := by decide +kernel
theorem check127 : AmplitudePolynomial.check scale ops epsilon panel127=true := by decide +kernel
end chebyshev2.Certificates.Compact.AmplitudeValues
