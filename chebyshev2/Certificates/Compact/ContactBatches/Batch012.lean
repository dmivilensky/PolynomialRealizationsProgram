import chebyshev2.Certificates.Compact.ContactBatches.Data012

/-!
Article: chebyshev2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 384–415.
Use: `chebyshev2.Certificates.Compact.ContactValues.residualCheck415` feeds
`chebyshev2.Certificates.Compact.ContactValues.valid415` (valid415).
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
theorem modelCheck384 : panel384.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck384 : ContactPolynomial.check scale ops epsilon panel384.row=true := by decide +kernel
theorem modelCheck385 : panel385.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck385 : ContactPolynomial.check scale ops epsilon panel385.row=true := by decide +kernel
theorem modelCheck386 : panel386.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck386 : ContactPolynomial.check scale ops epsilon panel386.row=true := by decide +kernel
theorem modelCheck387 : panel387.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck387 : ContactPolynomial.check scale ops epsilon panel387.row=true := by decide +kernel
theorem modelCheck388 : panel388.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck388 : ContactPolynomial.check scale ops epsilon panel388.row=true := by decide +kernel
theorem modelCheck389 : panel389.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck389 : ContactPolynomial.check scale ops epsilon panel389.row=true := by decide +kernel
theorem modelCheck390 : panel390.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck390 : ContactPolynomial.check scale ops epsilon panel390.row=true := by decide +kernel
theorem modelCheck391 : panel391.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck391 : ContactPolynomial.check scale ops epsilon panel391.row=true := by decide +kernel
theorem modelCheck392 : panel392.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck392 : ContactPolynomial.check scale ops epsilon panel392.row=true := by decide +kernel
theorem modelCheck393 : panel393.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck393 : ContactPolynomial.check scale ops epsilon panel393.row=true := by decide +kernel
theorem modelCheck394 : panel394.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck394 : ContactPolynomial.check scale ops epsilon panel394.row=true := by decide +kernel
theorem modelCheck395 : panel395.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck395 : ContactPolynomial.check scale ops epsilon panel395.row=true := by decide +kernel
theorem modelCheck396 : panel396.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck396 : ContactPolynomial.check scale ops epsilon panel396.row=true := by decide +kernel
theorem modelCheck397 : panel397.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck397 : ContactPolynomial.check scale ops epsilon panel397.row=true := by decide +kernel
theorem modelCheck398 : panel398.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck398 : ContactPolynomial.check scale ops epsilon panel398.row=true := by decide +kernel
theorem modelCheck399 : panel399.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck399 : ContactPolynomial.check scale ops epsilon panel399.row=true := by decide +kernel
theorem modelCheck400 : panel400.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck400 : ContactPolynomial.check scale ops epsilon panel400.row=true := by decide +kernel
theorem modelCheck401 : panel401.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck401 : ContactPolynomial.check scale ops epsilon panel401.row=true := by decide +kernel
theorem modelCheck402 : panel402.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck402 : ContactPolynomial.check scale ops epsilon panel402.row=true := by decide +kernel
theorem modelCheck403 : panel403.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck403 : ContactPolynomial.check scale ops epsilon panel403.row=true := by decide +kernel
theorem modelCheck404 : panel404.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck404 : ContactPolynomial.check scale ops epsilon panel404.row=true := by decide +kernel
theorem modelCheck405 : panel405.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck405 : ContactPolynomial.check scale ops epsilon panel405.row=true := by decide +kernel
theorem modelCheck406 : panel406.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck406 : ContactPolynomial.check scale ops epsilon panel406.row=true := by decide +kernel
theorem modelCheck407 : panel407.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck407 : ContactPolynomial.check scale ops epsilon panel407.row=true := by decide +kernel
theorem modelCheck408 : panel408.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck408 : ContactPolynomial.check scale ops epsilon panel408.row=true := by decide +kernel
theorem modelCheck409 : panel409.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck409 : ContactPolynomial.check scale ops epsilon panel409.row=true := by decide +kernel
theorem modelCheck410 : panel410.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck410 : ContactPolynomial.check scale ops epsilon panel410.row=true := by decide +kernel
theorem modelCheck411 : panel411.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck411 : ContactPolynomial.check scale ops epsilon panel411.row=true := by decide +kernel
theorem modelCheck412 : panel412.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck412 : ContactPolynomial.check scale ops epsilon panel412.row=true := by decide +kernel
theorem modelCheck413 : panel413.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck413 : ContactPolynomial.check scale ops epsilon panel413.row=true := by decide +kernel
theorem modelCheck414 : panel414.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck414 : ContactPolynomial.check scale ops epsilon panel414.row=true := by decide +kernel
theorem modelCheck415 : panel415.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck415 : ContactPolynomial.check scale ops epsilon panel415.row=true := by decide +kernel
end chebyshev2.Certificates.Compact.ContactValues
