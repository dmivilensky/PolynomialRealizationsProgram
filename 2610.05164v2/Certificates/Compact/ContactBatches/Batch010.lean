import «2610.05164v2».Certificates.Compact.ContactBatches.Data010

/-!
Article: 2610.05164v2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 320–351.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.residualCheck351` feeds
`«2610.05164v2».Certificates.Compact.ContactValues.valid351` (valid351).
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
theorem modelCheck320 : panel320.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck320 : ContactPolynomial.check scale ops epsilon panel320.row=true := by decide +kernel
theorem modelCheck321 : panel321.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck321 : ContactPolynomial.check scale ops epsilon panel321.row=true := by decide +kernel
theorem modelCheck322 : panel322.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck322 : ContactPolynomial.check scale ops epsilon panel322.row=true := by decide +kernel
theorem modelCheck323 : panel323.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck323 : ContactPolynomial.check scale ops epsilon panel323.row=true := by decide +kernel
theorem modelCheck324 : panel324.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck324 : ContactPolynomial.check scale ops epsilon panel324.row=true := by decide +kernel
theorem modelCheck325 : panel325.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck325 : ContactPolynomial.check scale ops epsilon panel325.row=true := by decide +kernel
theorem modelCheck326 : panel326.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck326 : ContactPolynomial.check scale ops epsilon panel326.row=true := by decide +kernel
theorem modelCheck327 : panel327.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck327 : ContactPolynomial.check scale ops epsilon panel327.row=true := by decide +kernel
theorem modelCheck328 : panel328.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck328 : ContactPolynomial.check scale ops epsilon panel328.row=true := by decide +kernel
theorem modelCheck329 : panel329.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck329 : ContactPolynomial.check scale ops epsilon panel329.row=true := by decide +kernel
theorem modelCheck330 : panel330.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck330 : ContactPolynomial.check scale ops epsilon panel330.row=true := by decide +kernel
theorem modelCheck331 : panel331.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck331 : ContactPolynomial.check scale ops epsilon panel331.row=true := by decide +kernel
theorem modelCheck332 : panel332.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck332 : ContactPolynomial.check scale ops epsilon panel332.row=true := by decide +kernel
theorem modelCheck333 : panel333.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck333 : ContactPolynomial.check scale ops epsilon panel333.row=true := by decide +kernel
theorem modelCheck334 : panel334.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck334 : ContactPolynomial.check scale ops epsilon panel334.row=true := by decide +kernel
theorem modelCheck335 : panel335.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck335 : ContactPolynomial.check scale ops epsilon panel335.row=true := by decide +kernel
theorem modelCheck336 : panel336.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck336 : ContactPolynomial.check scale ops epsilon panel336.row=true := by decide +kernel
theorem modelCheck337 : panel337.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck337 : ContactPolynomial.check scale ops epsilon panel337.row=true := by decide +kernel
theorem modelCheck338 : panel338.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck338 : ContactPolynomial.check scale ops epsilon panel338.row=true := by decide +kernel
theorem modelCheck339 : panel339.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck339 : ContactPolynomial.check scale ops epsilon panel339.row=true := by decide +kernel
theorem modelCheck340 : panel340.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck340 : ContactPolynomial.check scale ops epsilon panel340.row=true := by decide +kernel
theorem modelCheck341 : panel341.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck341 : ContactPolynomial.check scale ops epsilon panel341.row=true := by decide +kernel
theorem modelCheck342 : panel342.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck342 : ContactPolynomial.check scale ops epsilon panel342.row=true := by decide +kernel
theorem modelCheck343 : panel343.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck343 : ContactPolynomial.check scale ops epsilon panel343.row=true := by decide +kernel
theorem modelCheck344 : panel344.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck344 : ContactPolynomial.check scale ops epsilon panel344.row=true := by decide +kernel
theorem modelCheck345 : panel345.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck345 : ContactPolynomial.check scale ops epsilon panel345.row=true := by decide +kernel
theorem modelCheck346 : panel346.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck346 : ContactPolynomial.check scale ops epsilon panel346.row=true := by decide +kernel
theorem modelCheck347 : panel347.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck347 : ContactPolynomial.check scale ops epsilon panel347.row=true := by decide +kernel
theorem modelCheck348 : panel348.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck348 : ContactPolynomial.check scale ops epsilon panel348.row=true := by decide +kernel
theorem modelCheck349 : panel349.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck349 : ContactPolynomial.check scale ops epsilon panel349.row=true := by decide +kernel
theorem modelCheck350 : panel350.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck350 : ContactPolynomial.check scale ops epsilon panel350.row=true := by decide +kernel
theorem modelCheck351 : panel351.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck351 : ContactPolynomial.check scale ops epsilon panel351.row=true := by decide +kernel
end «2610.05164v2».Certificates.Compact.ContactValues
