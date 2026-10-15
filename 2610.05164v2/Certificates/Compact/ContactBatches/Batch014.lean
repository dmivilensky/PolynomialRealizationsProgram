import «2610.05164v2».Certificates.Compact.ContactBatches.Data014

/-!
Article: 2610.05164v2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 448–479.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.residualCheck479` feeds
`«2610.05164v2».Certificates.Compact.ContactValues.valid479` (valid479).
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
theorem modelCheck448 : panel448.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck448 : ContactPolynomial.check scale ops epsilon panel448.row=true := by decide +kernel
theorem modelCheck449 : panel449.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck449 : ContactPolynomial.check scale ops epsilon panel449.row=true := by decide +kernel
theorem modelCheck450 : panel450.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck450 : ContactPolynomial.check scale ops epsilon panel450.row=true := by decide +kernel
theorem modelCheck451 : panel451.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck451 : ContactPolynomial.check scale ops epsilon panel451.row=true := by decide +kernel
theorem modelCheck452 : panel452.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck452 : ContactPolynomial.check scale ops epsilon panel452.row=true := by decide +kernel
theorem modelCheck453 : panel453.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck453 : ContactPolynomial.check scale ops epsilon panel453.row=true := by decide +kernel
theorem modelCheck454 : panel454.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck454 : ContactPolynomial.check scale ops epsilon panel454.row=true := by decide +kernel
theorem modelCheck455 : panel455.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck455 : ContactPolynomial.check scale ops epsilon panel455.row=true := by decide +kernel
theorem modelCheck456 : panel456.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck456 : ContactPolynomial.check scale ops epsilon panel456.row=true := by decide +kernel
theorem modelCheck457 : panel457.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck457 : ContactPolynomial.check scale ops epsilon panel457.row=true := by decide +kernel
theorem modelCheck458 : panel458.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck458 : ContactPolynomial.check scale ops epsilon panel458.row=true := by decide +kernel
theorem modelCheck459 : panel459.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck459 : ContactPolynomial.check scale ops epsilon panel459.row=true := by decide +kernel
theorem modelCheck460 : panel460.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck460 : ContactPolynomial.check scale ops epsilon panel460.row=true := by decide +kernel
theorem modelCheck461 : panel461.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck461 : ContactPolynomial.check scale ops epsilon panel461.row=true := by decide +kernel
theorem modelCheck462 : panel462.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck462 : ContactPolynomial.check scale ops epsilon panel462.row=true := by decide +kernel
theorem modelCheck463 : panel463.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck463 : ContactPolynomial.check scale ops epsilon panel463.row=true := by decide +kernel
theorem modelCheck464 : panel464.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck464 : ContactPolynomial.check scale ops epsilon panel464.row=true := by decide +kernel
theorem modelCheck465 : panel465.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck465 : ContactPolynomial.check scale ops epsilon panel465.row=true := by decide +kernel
theorem modelCheck466 : panel466.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck466 : ContactPolynomial.check scale ops epsilon panel466.row=true := by decide +kernel
theorem modelCheck467 : panel467.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck467 : ContactPolynomial.check scale ops epsilon panel467.row=true := by decide +kernel
theorem modelCheck468 : panel468.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck468 : ContactPolynomial.check scale ops epsilon panel468.row=true := by decide +kernel
theorem modelCheck469 : panel469.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck469 : ContactPolynomial.check scale ops epsilon panel469.row=true := by decide +kernel
theorem modelCheck470 : panel470.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck470 : ContactPolynomial.check scale ops epsilon panel470.row=true := by decide +kernel
theorem modelCheck471 : panel471.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck471 : ContactPolynomial.check scale ops epsilon panel471.row=true := by decide +kernel
theorem modelCheck472 : panel472.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck472 : ContactPolynomial.check scale ops epsilon panel472.row=true := by decide +kernel
theorem modelCheck473 : panel473.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck473 : ContactPolynomial.check scale ops epsilon panel473.row=true := by decide +kernel
theorem modelCheck474 : panel474.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck474 : ContactPolynomial.check scale ops epsilon panel474.row=true := by decide +kernel
theorem modelCheck475 : panel475.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck475 : ContactPolynomial.check scale ops epsilon panel475.row=true := by decide +kernel
theorem modelCheck476 : panel476.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck476 : ContactPolynomial.check scale ops epsilon panel476.row=true := by decide +kernel
theorem modelCheck477 : panel477.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck477 : ContactPolynomial.check scale ops epsilon panel477.row=true := by decide +kernel
theorem modelCheck478 : panel478.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck478 : ContactPolynomial.check scale ops epsilon panel478.row=true := by decide +kernel
theorem modelCheck479 : panel479.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck479 : ContactPolynomial.check scale ops epsilon panel479.row=true := by decide +kernel
end «2610.05164v2».Certificates.Compact.ContactValues
