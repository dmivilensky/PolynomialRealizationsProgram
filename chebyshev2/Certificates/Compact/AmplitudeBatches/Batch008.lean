import chebyshev2.Certificates.Compact.AmplitudeBatches.Data008

/-!
Article: chebyshev2, Section 4.1.
Kernel reduction of acceptance for amplitude quadrature panels 256–287.
Use: `chebyshev2.Certificates.Compact.AmplitudeValues.check287` feeds
`chebyshev2.Certificates.Compact.AmplitudeValues.valid287` (valid287).
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
theorem check256 : AmplitudePolynomial.check scale ops epsilon panel256=true := by decide +kernel
theorem check257 : AmplitudePolynomial.check scale ops epsilon panel257=true := by decide +kernel
theorem check258 : AmplitudePolynomial.check scale ops epsilon panel258=true := by decide +kernel
theorem check259 : AmplitudePolynomial.check scale ops epsilon panel259=true := by decide +kernel
theorem check260 : AmplitudePolynomial.check scale ops epsilon panel260=true := by decide +kernel
theorem check261 : AmplitudePolynomial.check scale ops epsilon panel261=true := by decide +kernel
theorem check262 : AmplitudePolynomial.check scale ops epsilon panel262=true := by decide +kernel
theorem check263 : AmplitudePolynomial.check scale ops epsilon panel263=true := by decide +kernel
theorem check264 : AmplitudePolynomial.check scale ops epsilon panel264=true := by decide +kernel
theorem check265 : AmplitudePolynomial.check scale ops epsilon panel265=true := by decide +kernel
theorem check266 : AmplitudePolynomial.check scale ops epsilon panel266=true := by decide +kernel
theorem check267 : AmplitudePolynomial.check scale ops epsilon panel267=true := by decide +kernel
theorem check268 : AmplitudePolynomial.check scale ops epsilon panel268=true := by decide +kernel
theorem check269 : AmplitudePolynomial.check scale ops epsilon panel269=true := by decide +kernel
theorem check270 : AmplitudePolynomial.check scale ops epsilon panel270=true := by decide +kernel
theorem check271 : AmplitudePolynomial.check scale ops epsilon panel271=true := by decide +kernel
theorem check272 : AmplitudePolynomial.check scale ops epsilon panel272=true := by decide +kernel
theorem check273 : AmplitudePolynomial.check scale ops epsilon panel273=true := by decide +kernel
theorem check274 : AmplitudePolynomial.check scale ops epsilon panel274=true := by decide +kernel
theorem check275 : AmplitudePolynomial.check scale ops epsilon panel275=true := by decide +kernel
theorem check276 : AmplitudePolynomial.check scale ops epsilon panel276=true := by decide +kernel
theorem check277 : AmplitudePolynomial.check scale ops epsilon panel277=true := by decide +kernel
theorem check278 : AmplitudePolynomial.check scale ops epsilon panel278=true := by decide +kernel
theorem check279 : AmplitudePolynomial.check scale ops epsilon panel279=true := by decide +kernel
theorem check280 : AmplitudePolynomial.check scale ops epsilon panel280=true := by decide +kernel
theorem check281 : AmplitudePolynomial.check scale ops epsilon panel281=true := by decide +kernel
theorem check282 : AmplitudePolynomial.check scale ops epsilon panel282=true := by decide +kernel
theorem check283 : AmplitudePolynomial.check scale ops epsilon panel283=true := by decide +kernel
theorem check284 : AmplitudePolynomial.check scale ops epsilon panel284=true := by decide +kernel
theorem check285 : AmplitudePolynomial.check scale ops epsilon panel285=true := by decide +kernel
theorem check286 : AmplitudePolynomial.check scale ops epsilon panel286=true := by decide +kernel
theorem check287 : AmplitudePolynomial.check scale ops epsilon panel287=true := by decide +kernel
end chebyshev2.Certificates.Compact.AmplitudeValues
