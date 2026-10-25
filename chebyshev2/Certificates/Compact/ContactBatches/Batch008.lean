import chebyshev2.Certificates.Compact.ContactBatches.Data008

/-!
Article: chebyshev2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 256–287.
Use: `chebyshev2.Certificates.Compact.ContactValues.residualCheck287` feeds
`chebyshev2.Certificates.Compact.ContactValues.valid287` (valid287).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace chebyshev2.Certificates.Compact.ContactValues
open chebyshev2.Numerics chebyshev2.Numerics.IntegerCertificate
theorem modelCheck256 : panel256.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck256 : ContactPolynomial.check scale ops epsilon panel256.row=true := by decide +kernel
theorem modelCheck257 : panel257.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck257 : ContactPolynomial.check scale ops epsilon panel257.row=true := by decide +kernel
theorem modelCheck258 : panel258.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck258 : ContactPolynomial.check scale ops epsilon panel258.row=true := by decide +kernel
theorem modelCheck259 : panel259.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck259 : ContactPolynomial.check scale ops epsilon panel259.row=true := by decide +kernel
theorem modelCheck260 : panel260.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck260 : ContactPolynomial.check scale ops epsilon panel260.row=true := by decide +kernel
theorem modelCheck261 : panel261.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck261 : ContactPolynomial.check scale ops epsilon panel261.row=true := by decide +kernel
theorem modelCheck262 : panel262.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck262 : ContactPolynomial.check scale ops epsilon panel262.row=true := by decide +kernel
theorem modelCheck263 : panel263.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck263 : ContactPolynomial.check scale ops epsilon panel263.row=true := by decide +kernel
theorem modelCheck264 : panel264.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck264 : ContactPolynomial.check scale ops epsilon panel264.row=true := by decide +kernel
theorem modelCheck265 : panel265.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck265 : ContactPolynomial.check scale ops epsilon panel265.row=true := by decide +kernel
theorem modelCheck266 : panel266.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck266 : ContactPolynomial.check scale ops epsilon panel266.row=true := by decide +kernel
theorem modelCheck267 : panel267.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck267 : ContactPolynomial.check scale ops epsilon panel267.row=true := by decide +kernel
theorem modelCheck268 : panel268.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck268 : ContactPolynomial.check scale ops epsilon panel268.row=true := by decide +kernel
theorem modelCheck269 : panel269.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck269 : ContactPolynomial.check scale ops epsilon panel269.row=true := by decide +kernel
theorem modelCheck270 : panel270.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck270 : ContactPolynomial.check scale ops epsilon panel270.row=true := by decide +kernel
theorem modelCheck271 : panel271.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck271 : ContactPolynomial.check scale ops epsilon panel271.row=true := by decide +kernel
theorem modelCheck272 : panel272.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck272 : ContactPolynomial.check scale ops epsilon panel272.row=true := by decide +kernel
theorem modelCheck273 : panel273.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck273 : ContactPolynomial.check scale ops epsilon panel273.row=true := by decide +kernel
theorem modelCheck274 : panel274.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck274 : ContactPolynomial.check scale ops epsilon panel274.row=true := by decide +kernel
theorem modelCheck275 : panel275.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck275 : ContactPolynomial.check scale ops epsilon panel275.row=true := by decide +kernel
theorem modelCheck276 : panel276.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck276 : ContactPolynomial.check scale ops epsilon panel276.row=true := by decide +kernel
theorem modelCheck277 : panel277.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck277 : ContactPolynomial.check scale ops epsilon panel277.row=true := by decide +kernel
theorem modelCheck278 : panel278.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck278 : ContactPolynomial.check scale ops epsilon panel278.row=true := by decide +kernel
theorem modelCheck279 : panel279.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck279 : ContactPolynomial.check scale ops epsilon panel279.row=true := by decide +kernel
theorem modelCheck280 : panel280.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck280 : ContactPolynomial.check scale ops epsilon panel280.row=true := by decide +kernel
theorem modelCheck281 : panel281.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck281 : ContactPolynomial.check scale ops epsilon panel281.row=true := by decide +kernel
theorem modelCheck282 : panel282.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck282 : ContactPolynomial.check scale ops epsilon panel282.row=true := by decide +kernel
theorem modelCheck283 : panel283.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck283 : ContactPolynomial.check scale ops epsilon panel283.row=true := by decide +kernel
theorem modelCheck284 : panel284.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck284 : ContactPolynomial.check scale ops epsilon panel284.row=true := by decide +kernel
theorem modelCheck285 : panel285.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck285 : ContactPolynomial.check scale ops epsilon panel285.row=true := by decide +kernel
theorem modelCheck286 : panel286.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck286 : ContactPolynomial.check scale ops epsilon panel286.row=true := by decide +kernel
theorem modelCheck287 : panel287.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck287 : ContactPolynomial.check scale ops epsilon panel287.row=true := by decide +kernel
end chebyshev2.Certificates.Compact.ContactValues
