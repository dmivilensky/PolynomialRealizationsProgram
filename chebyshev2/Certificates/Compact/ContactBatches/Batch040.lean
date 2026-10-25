import chebyshev2.Certificates.Compact.ContactBatches.Data040

/-!
Article: chebyshev2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 1280–1290.
Use: `chebyshev2.Certificates.Compact.ContactValues.residualCheck1290` feeds
`chebyshev2.Certificates.Compact.ContactValues.valid1290` (valid1290).
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
theorem modelCheck1280 : panel1280.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1280 : ContactPolynomial.check scale ops epsilon panel1280.row=true := by decide +kernel
theorem modelCheck1281 : panel1281.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1281 : ContactPolynomial.check scale ops epsilon panel1281.row=true := by decide +kernel
theorem modelCheck1282 : panel1282.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1282 : ContactPolynomial.check scale ops epsilon panel1282.row=true := by decide +kernel
theorem modelCheck1283 : panel1283.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1283 : ContactPolynomial.check scale ops epsilon panel1283.row=true := by decide +kernel
theorem modelCheck1284 : panel1284.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1284 : ContactPolynomial.check scale ops epsilon panel1284.row=true := by decide +kernel
theorem modelCheck1285 : panel1285.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1285 : ContactPolynomial.check scale ops epsilon panel1285.row=true := by decide +kernel
theorem modelCheck1286 : panel1286.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1286 : ContactPolynomial.check scale ops epsilon panel1286.row=true := by decide +kernel
theorem modelCheck1287 : panel1287.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1287 : ContactPolynomial.check scale ops epsilon panel1287.row=true := by decide +kernel
theorem modelCheck1288 : panel1288.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1288 : ContactPolynomial.check scale ops epsilon panel1288.row=true := by decide +kernel
theorem modelCheck1289 : panel1289.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1289 : ContactPolynomial.check scale ops epsilon panel1289.row=true := by decide +kernel
theorem modelCheck1290 : panel1290.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1290 : ContactPolynomial.check scale ops epsilon panel1290.row=true := by decide +kernel
end chebyshev2.Certificates.Compact.ContactValues
