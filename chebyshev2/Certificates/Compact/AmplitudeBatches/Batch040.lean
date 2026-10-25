import chebyshev2.Certificates.Compact.AmplitudeBatches.Data040

/-!
Article: chebyshev2, Section 4.1.
Kernel reduction of acceptance for amplitude quadrature panels 1280–1290.
Use: `chebyshev2.Certificates.Compact.AmplitudeValues.check1290` feeds
`chebyshev2.Certificates.Compact.AmplitudeValues.valid1290` (valid1290).
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
theorem check1280 : AmplitudePolynomial.check scale ops epsilon panel1280=true := by decide +kernel
theorem check1281 : AmplitudePolynomial.check scale ops epsilon panel1281=true := by decide +kernel
theorem check1282 : AmplitudePolynomial.check scale ops epsilon panel1282=true := by decide +kernel
theorem check1283 : AmplitudePolynomial.check scale ops epsilon panel1283=true := by decide +kernel
theorem check1284 : AmplitudePolynomial.check scale ops epsilon panel1284=true := by decide +kernel
theorem check1285 : AmplitudePolynomial.check scale ops epsilon panel1285=true := by decide +kernel
theorem check1286 : AmplitudePolynomial.check scale ops epsilon panel1286=true := by decide +kernel
theorem check1287 : AmplitudePolynomial.check scale ops epsilon panel1287=true := by decide +kernel
theorem check1288 : AmplitudePolynomial.check scale ops epsilon panel1288=true := by decide +kernel
theorem check1289 : AmplitudePolynomial.check scale ops epsilon panel1289=true := by decide +kernel
theorem check1290 : AmplitudePolynomial.check scale ops epsilon panel1290=true := by decide +kernel
end chebyshev2.Certificates.Compact.AmplitudeValues
