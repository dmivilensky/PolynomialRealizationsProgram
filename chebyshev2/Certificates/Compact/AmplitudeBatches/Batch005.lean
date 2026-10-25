import chebyshev2.Certificates.Compact.AmplitudeBatches.Data005

/-!
Article: chebyshev2, Section 4.1.
Kernel reduction of acceptance for amplitude quadrature panels 160–191.
Use: `chebyshev2.Certificates.Compact.AmplitudeValues.check191` feeds
`chebyshev2.Certificates.Compact.AmplitudeValues.valid191` (valid191).
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
theorem check160 : AmplitudePolynomial.check scale ops epsilon panel160=true := by decide +kernel
theorem check161 : AmplitudePolynomial.check scale ops epsilon panel161=true := by decide +kernel
theorem check162 : AmplitudePolynomial.check scale ops epsilon panel162=true := by decide +kernel
theorem check163 : AmplitudePolynomial.check scale ops epsilon panel163=true := by decide +kernel
theorem check164 : AmplitudePolynomial.check scale ops epsilon panel164=true := by decide +kernel
theorem check165 : AmplitudePolynomial.check scale ops epsilon panel165=true := by decide +kernel
theorem check166 : AmplitudePolynomial.check scale ops epsilon panel166=true := by decide +kernel
theorem check167 : AmplitudePolynomial.check scale ops epsilon panel167=true := by decide +kernel
theorem check168 : AmplitudePolynomial.check scale ops epsilon panel168=true := by decide +kernel
theorem check169 : AmplitudePolynomial.check scale ops epsilon panel169=true := by decide +kernel
theorem check170 : AmplitudePolynomial.check scale ops epsilon panel170=true := by decide +kernel
theorem check171 : AmplitudePolynomial.check scale ops epsilon panel171=true := by decide +kernel
theorem check172 : AmplitudePolynomial.check scale ops epsilon panel172=true := by decide +kernel
theorem check173 : AmplitudePolynomial.check scale ops epsilon panel173=true := by decide +kernel
theorem check174 : AmplitudePolynomial.check scale ops epsilon panel174=true := by decide +kernel
theorem check175 : AmplitudePolynomial.check scale ops epsilon panel175=true := by decide +kernel
theorem check176 : AmplitudePolynomial.check scale ops epsilon panel176=true := by decide +kernel
theorem check177 : AmplitudePolynomial.check scale ops epsilon panel177=true := by decide +kernel
theorem check178 : AmplitudePolynomial.check scale ops epsilon panel178=true := by decide +kernel
theorem check179 : AmplitudePolynomial.check scale ops epsilon panel179=true := by decide +kernel
theorem check180 : AmplitudePolynomial.check scale ops epsilon panel180=true := by decide +kernel
theorem check181 : AmplitudePolynomial.check scale ops epsilon panel181=true := by decide +kernel
theorem check182 : AmplitudePolynomial.check scale ops epsilon panel182=true := by decide +kernel
theorem check183 : AmplitudePolynomial.check scale ops epsilon panel183=true := by decide +kernel
theorem check184 : AmplitudePolynomial.check scale ops epsilon panel184=true := by decide +kernel
theorem check185 : AmplitudePolynomial.check scale ops epsilon panel185=true := by decide +kernel
theorem check186 : AmplitudePolynomial.check scale ops epsilon panel186=true := by decide +kernel
theorem check187 : AmplitudePolynomial.check scale ops epsilon panel187=true := by decide +kernel
theorem check188 : AmplitudePolynomial.check scale ops epsilon panel188=true := by decide +kernel
theorem check189 : AmplitudePolynomial.check scale ops epsilon panel189=true := by decide +kernel
theorem check190 : AmplitudePolynomial.check scale ops epsilon panel190=true := by decide +kernel
theorem check191 : AmplitudePolynomial.check scale ops epsilon panel191=true := by decide +kernel
end chebyshev2.Certificates.Compact.AmplitudeValues
