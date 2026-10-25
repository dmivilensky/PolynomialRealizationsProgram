import chebyshev2.Certificates.Compact.AmplitudeBatches.Data007

/-!
Article: chebyshev2, Section 4.1.
Kernel reduction of acceptance for amplitude quadrature panels 224–255.
Use: `chebyshev2.Certificates.Compact.AmplitudeValues.check255` feeds
`chebyshev2.Certificates.Compact.AmplitudeValues.valid255` (valid255).
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
theorem check224 : AmplitudePolynomial.check scale ops epsilon panel224=true := by decide +kernel
theorem check225 : AmplitudePolynomial.check scale ops epsilon panel225=true := by decide +kernel
theorem check226 : AmplitudePolynomial.check scale ops epsilon panel226=true := by decide +kernel
theorem check227 : AmplitudePolynomial.check scale ops epsilon panel227=true := by decide +kernel
theorem check228 : AmplitudePolynomial.check scale ops epsilon panel228=true := by decide +kernel
theorem check229 : AmplitudePolynomial.check scale ops epsilon panel229=true := by decide +kernel
theorem check230 : AmplitudePolynomial.check scale ops epsilon panel230=true := by decide +kernel
theorem check231 : AmplitudePolynomial.check scale ops epsilon panel231=true := by decide +kernel
theorem check232 : AmplitudePolynomial.check scale ops epsilon panel232=true := by decide +kernel
theorem check233 : AmplitudePolynomial.check scale ops epsilon panel233=true := by decide +kernel
theorem check234 : AmplitudePolynomial.check scale ops epsilon panel234=true := by decide +kernel
theorem check235 : AmplitudePolynomial.check scale ops epsilon panel235=true := by decide +kernel
theorem check236 : AmplitudePolynomial.check scale ops epsilon panel236=true := by decide +kernel
theorem check237 : AmplitudePolynomial.check scale ops epsilon panel237=true := by decide +kernel
theorem check238 : AmplitudePolynomial.check scale ops epsilon panel238=true := by decide +kernel
theorem check239 : AmplitudePolynomial.check scale ops epsilon panel239=true := by decide +kernel
theorem check240 : AmplitudePolynomial.check scale ops epsilon panel240=true := by decide +kernel
theorem check241 : AmplitudePolynomial.check scale ops epsilon panel241=true := by decide +kernel
theorem check242 : AmplitudePolynomial.check scale ops epsilon panel242=true := by decide +kernel
theorem check243 : AmplitudePolynomial.check scale ops epsilon panel243=true := by decide +kernel
theorem check244 : AmplitudePolynomial.check scale ops epsilon panel244=true := by decide +kernel
theorem check245 : AmplitudePolynomial.check scale ops epsilon panel245=true := by decide +kernel
theorem check246 : AmplitudePolynomial.check scale ops epsilon panel246=true := by decide +kernel
theorem check247 : AmplitudePolynomial.check scale ops epsilon panel247=true := by decide +kernel
theorem check248 : AmplitudePolynomial.check scale ops epsilon panel248=true := by decide +kernel
theorem check249 : AmplitudePolynomial.check scale ops epsilon panel249=true := by decide +kernel
theorem check250 : AmplitudePolynomial.check scale ops epsilon panel250=true := by decide +kernel
theorem check251 : AmplitudePolynomial.check scale ops epsilon panel251=true := by decide +kernel
theorem check252 : AmplitudePolynomial.check scale ops epsilon panel252=true := by decide +kernel
theorem check253 : AmplitudePolynomial.check scale ops epsilon panel253=true := by decide +kernel
theorem check254 : AmplitudePolynomial.check scale ops epsilon panel254=true := by decide +kernel
theorem check255 : AmplitudePolynomial.check scale ops epsilon panel255=true := by decide +kernel
end chebyshev2.Certificates.Compact.AmplitudeValues
