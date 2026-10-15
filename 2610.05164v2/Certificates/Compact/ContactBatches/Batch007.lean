import «2610.05164v2».Certificates.Compact.ContactBatches.Data007

/-!
Article: 2610.05164v2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 224–255.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.residualCheck255` feeds
`«2610.05164v2».Certificates.Compact.ContactValues.valid255` (valid255).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace «2610.05164v2».Certificates.Compact.ContactValues
open «2610.05164v2».Numerics «2610.05164v2».Numerics.IntegerCertificate
theorem modelCheck224 : panel224.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck224 : ContactPolynomial.check scale ops epsilon panel224.row=true := by decide +kernel
theorem modelCheck225 : panel225.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck225 : ContactPolynomial.check scale ops epsilon panel225.row=true := by decide +kernel
theorem modelCheck226 : panel226.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck226 : ContactPolynomial.check scale ops epsilon panel226.row=true := by decide +kernel
theorem modelCheck227 : panel227.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck227 : ContactPolynomial.check scale ops epsilon panel227.row=true := by decide +kernel
theorem modelCheck228 : panel228.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck228 : ContactPolynomial.check scale ops epsilon panel228.row=true := by decide +kernel
theorem modelCheck229 : panel229.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck229 : ContactPolynomial.check scale ops epsilon panel229.row=true := by decide +kernel
theorem modelCheck230 : panel230.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck230 : ContactPolynomial.check scale ops epsilon panel230.row=true := by decide +kernel
theorem modelCheck231 : panel231.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck231 : ContactPolynomial.check scale ops epsilon panel231.row=true := by decide +kernel
theorem modelCheck232 : panel232.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck232 : ContactPolynomial.check scale ops epsilon panel232.row=true := by decide +kernel
theorem modelCheck233 : panel233.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck233 : ContactPolynomial.check scale ops epsilon panel233.row=true := by decide +kernel
theorem modelCheck234 : panel234.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck234 : ContactPolynomial.check scale ops epsilon panel234.row=true := by decide +kernel
theorem modelCheck235 : panel235.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck235 : ContactPolynomial.check scale ops epsilon panel235.row=true := by decide +kernel
theorem modelCheck236 : panel236.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck236 : ContactPolynomial.check scale ops epsilon panel236.row=true := by decide +kernel
theorem modelCheck237 : panel237.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck237 : ContactPolynomial.check scale ops epsilon panel237.row=true := by decide +kernel
theorem modelCheck238 : panel238.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck238 : ContactPolynomial.check scale ops epsilon panel238.row=true := by decide +kernel
theorem modelCheck239 : panel239.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck239 : ContactPolynomial.check scale ops epsilon panel239.row=true := by decide +kernel
theorem modelCheck240 : panel240.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck240 : ContactPolynomial.check scale ops epsilon panel240.row=true := by decide +kernel
theorem modelCheck241 : panel241.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck241 : ContactPolynomial.check scale ops epsilon panel241.row=true := by decide +kernel
theorem modelCheck242 : panel242.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck242 : ContactPolynomial.check scale ops epsilon panel242.row=true := by decide +kernel
theorem modelCheck243 : panel243.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck243 : ContactPolynomial.check scale ops epsilon panel243.row=true := by decide +kernel
theorem modelCheck244 : panel244.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck244 : ContactPolynomial.check scale ops epsilon panel244.row=true := by decide +kernel
theorem modelCheck245 : panel245.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck245 : ContactPolynomial.check scale ops epsilon panel245.row=true := by decide +kernel
theorem modelCheck246 : panel246.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck246 : ContactPolynomial.check scale ops epsilon panel246.row=true := by decide +kernel
theorem modelCheck247 : panel247.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck247 : ContactPolynomial.check scale ops epsilon panel247.row=true := by decide +kernel
theorem modelCheck248 : panel248.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck248 : ContactPolynomial.check scale ops epsilon panel248.row=true := by decide +kernel
theorem modelCheck249 : panel249.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck249 : ContactPolynomial.check scale ops epsilon panel249.row=true := by decide +kernel
theorem modelCheck250 : panel250.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck250 : ContactPolynomial.check scale ops epsilon panel250.row=true := by decide +kernel
theorem modelCheck251 : panel251.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck251 : ContactPolynomial.check scale ops epsilon panel251.row=true := by decide +kernel
theorem modelCheck252 : panel252.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck252 : ContactPolynomial.check scale ops epsilon panel252.row=true := by decide +kernel
theorem modelCheck253 : panel253.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck253 : ContactPolynomial.check scale ops epsilon panel253.row=true := by decide +kernel
theorem modelCheck254 : panel254.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck254 : ContactPolynomial.check scale ops epsilon panel254.row=true := by decide +kernel
theorem modelCheck255 : panel255.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck255 : ContactPolynomial.check scale ops epsilon panel255.row=true := by decide +kernel
end «2610.05164v2».Certificates.Compact.ContactValues
