import «2610.05164v2».Certificates.Compact.ContactBatches.Data011

/-!
Article: 2610.05164v2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 352–383.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.residualCheck383` feeds
`«2610.05164v2».Certificates.Compact.ContactValues.valid383` (valid383).
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
theorem modelCheck352 : panel352.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck352 : ContactPolynomial.check scale ops epsilon panel352.row=true := by decide +kernel
theorem modelCheck353 : panel353.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck353 : ContactPolynomial.check scale ops epsilon panel353.row=true := by decide +kernel
theorem modelCheck354 : panel354.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck354 : ContactPolynomial.check scale ops epsilon panel354.row=true := by decide +kernel
theorem modelCheck355 : panel355.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck355 : ContactPolynomial.check scale ops epsilon panel355.row=true := by decide +kernel
theorem modelCheck356 : panel356.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck356 : ContactPolynomial.check scale ops epsilon panel356.row=true := by decide +kernel
theorem modelCheck357 : panel357.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck357 : ContactPolynomial.check scale ops epsilon panel357.row=true := by decide +kernel
theorem modelCheck358 : panel358.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck358 : ContactPolynomial.check scale ops epsilon panel358.row=true := by decide +kernel
theorem modelCheck359 : panel359.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck359 : ContactPolynomial.check scale ops epsilon panel359.row=true := by decide +kernel
theorem modelCheck360 : panel360.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck360 : ContactPolynomial.check scale ops epsilon panel360.row=true := by decide +kernel
theorem modelCheck361 : panel361.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck361 : ContactPolynomial.check scale ops epsilon panel361.row=true := by decide +kernel
theorem modelCheck362 : panel362.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck362 : ContactPolynomial.check scale ops epsilon panel362.row=true := by decide +kernel
theorem modelCheck363 : panel363.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck363 : ContactPolynomial.check scale ops epsilon panel363.row=true := by decide +kernel
theorem modelCheck364 : panel364.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck364 : ContactPolynomial.check scale ops epsilon panel364.row=true := by decide +kernel
theorem modelCheck365 : panel365.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck365 : ContactPolynomial.check scale ops epsilon panel365.row=true := by decide +kernel
theorem modelCheck366 : panel366.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck366 : ContactPolynomial.check scale ops epsilon panel366.row=true := by decide +kernel
theorem modelCheck367 : panel367.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck367 : ContactPolynomial.check scale ops epsilon panel367.row=true := by decide +kernel
theorem modelCheck368 : panel368.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck368 : ContactPolynomial.check scale ops epsilon panel368.row=true := by decide +kernel
theorem modelCheck369 : panel369.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck369 : ContactPolynomial.check scale ops epsilon panel369.row=true := by decide +kernel
theorem modelCheck370 : panel370.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck370 : ContactPolynomial.check scale ops epsilon panel370.row=true := by decide +kernel
theorem modelCheck371 : panel371.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck371 : ContactPolynomial.check scale ops epsilon panel371.row=true := by decide +kernel
theorem modelCheck372 : panel372.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck372 : ContactPolynomial.check scale ops epsilon panel372.row=true := by decide +kernel
theorem modelCheck373 : panel373.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck373 : ContactPolynomial.check scale ops epsilon panel373.row=true := by decide +kernel
theorem modelCheck374 : panel374.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck374 : ContactPolynomial.check scale ops epsilon panel374.row=true := by decide +kernel
theorem modelCheck375 : panel375.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck375 : ContactPolynomial.check scale ops epsilon panel375.row=true := by decide +kernel
theorem modelCheck376 : panel376.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck376 : ContactPolynomial.check scale ops epsilon panel376.row=true := by decide +kernel
theorem modelCheck377 : panel377.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck377 : ContactPolynomial.check scale ops epsilon panel377.row=true := by decide +kernel
theorem modelCheck378 : panel378.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck378 : ContactPolynomial.check scale ops epsilon panel378.row=true := by decide +kernel
theorem modelCheck379 : panel379.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck379 : ContactPolynomial.check scale ops epsilon panel379.row=true := by decide +kernel
theorem modelCheck380 : panel380.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck380 : ContactPolynomial.check scale ops epsilon panel380.row=true := by decide +kernel
theorem modelCheck381 : panel381.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck381 : ContactPolynomial.check scale ops epsilon panel381.row=true := by decide +kernel
theorem modelCheck382 : panel382.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck382 : ContactPolynomial.check scale ops epsilon panel382.row=true := by decide +kernel
theorem modelCheck383 : panel383.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck383 : ContactPolynomial.check scale ops epsilon panel383.row=true := by decide +kernel
end «2610.05164v2».Certificates.Compact.ContactValues
