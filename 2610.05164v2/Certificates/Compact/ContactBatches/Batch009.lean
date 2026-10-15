import «2610.05164v2».Certificates.Compact.ContactBatches.Data009

/-!
Article: 2610.05164v2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 288–319.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.residualCheck319` feeds
`«2610.05164v2».Certificates.Compact.ContactValues.valid319` (valid319).
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
theorem modelCheck288 : panel288.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck288 : ContactPolynomial.check scale ops epsilon panel288.row=true := by decide +kernel
theorem modelCheck289 : panel289.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck289 : ContactPolynomial.check scale ops epsilon panel289.row=true := by decide +kernel
theorem modelCheck290 : panel290.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck290 : ContactPolynomial.check scale ops epsilon panel290.row=true := by decide +kernel
theorem modelCheck291 : panel291.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck291 : ContactPolynomial.check scale ops epsilon panel291.row=true := by decide +kernel
theorem modelCheck292 : panel292.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck292 : ContactPolynomial.check scale ops epsilon panel292.row=true := by decide +kernel
theorem modelCheck293 : panel293.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck293 : ContactPolynomial.check scale ops epsilon panel293.row=true := by decide +kernel
theorem modelCheck294 : panel294.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck294 : ContactPolynomial.check scale ops epsilon panel294.row=true := by decide +kernel
theorem modelCheck295 : panel295.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck295 : ContactPolynomial.check scale ops epsilon panel295.row=true := by decide +kernel
theorem modelCheck296 : panel296.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck296 : ContactPolynomial.check scale ops epsilon panel296.row=true := by decide +kernel
theorem modelCheck297 : panel297.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck297 : ContactPolynomial.check scale ops epsilon panel297.row=true := by decide +kernel
theorem modelCheck298 : panel298.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck298 : ContactPolynomial.check scale ops epsilon panel298.row=true := by decide +kernel
theorem modelCheck299 : panel299.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck299 : ContactPolynomial.check scale ops epsilon panel299.row=true := by decide +kernel
theorem modelCheck300 : panel300.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck300 : ContactPolynomial.check scale ops epsilon panel300.row=true := by decide +kernel
theorem modelCheck301 : panel301.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck301 : ContactPolynomial.check scale ops epsilon panel301.row=true := by decide +kernel
theorem modelCheck302 : panel302.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck302 : ContactPolynomial.check scale ops epsilon panel302.row=true := by decide +kernel
theorem modelCheck303 : panel303.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck303 : ContactPolynomial.check scale ops epsilon panel303.row=true := by decide +kernel
theorem modelCheck304 : panel304.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck304 : ContactPolynomial.check scale ops epsilon panel304.row=true := by decide +kernel
theorem modelCheck305 : panel305.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck305 : ContactPolynomial.check scale ops epsilon panel305.row=true := by decide +kernel
theorem modelCheck306 : panel306.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck306 : ContactPolynomial.check scale ops epsilon panel306.row=true := by decide +kernel
theorem modelCheck307 : panel307.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck307 : ContactPolynomial.check scale ops epsilon panel307.row=true := by decide +kernel
theorem modelCheck308 : panel308.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck308 : ContactPolynomial.check scale ops epsilon panel308.row=true := by decide +kernel
theorem modelCheck309 : panel309.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck309 : ContactPolynomial.check scale ops epsilon panel309.row=true := by decide +kernel
theorem modelCheck310 : panel310.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck310 : ContactPolynomial.check scale ops epsilon panel310.row=true := by decide +kernel
theorem modelCheck311 : panel311.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck311 : ContactPolynomial.check scale ops epsilon panel311.row=true := by decide +kernel
theorem modelCheck312 : panel312.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck312 : ContactPolynomial.check scale ops epsilon panel312.row=true := by decide +kernel
theorem modelCheck313 : panel313.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck313 : ContactPolynomial.check scale ops epsilon panel313.row=true := by decide +kernel
theorem modelCheck314 : panel314.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck314 : ContactPolynomial.check scale ops epsilon panel314.row=true := by decide +kernel
theorem modelCheck315 : panel315.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck315 : ContactPolynomial.check scale ops epsilon panel315.row=true := by decide +kernel
theorem modelCheck316 : panel316.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck316 : ContactPolynomial.check scale ops epsilon panel316.row=true := by decide +kernel
theorem modelCheck317 : panel317.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck317 : ContactPolynomial.check scale ops epsilon panel317.row=true := by decide +kernel
theorem modelCheck318 : panel318.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck318 : ContactPolynomial.check scale ops epsilon panel318.row=true := by decide +kernel
theorem modelCheck319 : panel319.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck319 : ContactPolynomial.check scale ops epsilon panel319.row=true := by decide +kernel
end «2610.05164v2».Certificates.Compact.ContactValues
