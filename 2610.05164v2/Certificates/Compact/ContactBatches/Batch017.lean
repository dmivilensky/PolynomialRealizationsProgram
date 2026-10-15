import «2610.05164v2».Certificates.Compact.ContactBatches.Data017

/-!
Article: 2610.05164v2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 544–575.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.residualCheck575` feeds
`«2610.05164v2».Certificates.Compact.ContactValues.valid575` (valid575).
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
theorem modelCheck544 : panel544.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck544 : ContactPolynomial.check scale ops epsilon panel544.row=true := by decide +kernel
theorem modelCheck545 : panel545.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck545 : ContactPolynomial.check scale ops epsilon panel545.row=true := by decide +kernel
theorem modelCheck546 : panel546.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck546 : ContactPolynomial.check scale ops epsilon panel546.row=true := by decide +kernel
theorem modelCheck547 : panel547.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck547 : ContactPolynomial.check scale ops epsilon panel547.row=true := by decide +kernel
theorem modelCheck548 : panel548.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck548 : ContactPolynomial.check scale ops epsilon panel548.row=true := by decide +kernel
theorem modelCheck549 : panel549.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck549 : ContactPolynomial.check scale ops epsilon panel549.row=true := by decide +kernel
theorem modelCheck550 : panel550.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck550 : ContactPolynomial.check scale ops epsilon panel550.row=true := by decide +kernel
theorem modelCheck551 : panel551.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck551 : ContactPolynomial.check scale ops epsilon panel551.row=true := by decide +kernel
theorem modelCheck552 : panel552.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck552 : ContactPolynomial.check scale ops epsilon panel552.row=true := by decide +kernel
theorem modelCheck553 : panel553.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck553 : ContactPolynomial.check scale ops epsilon panel553.row=true := by decide +kernel
theorem modelCheck554 : panel554.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck554 : ContactPolynomial.check scale ops epsilon panel554.row=true := by decide +kernel
theorem modelCheck555 : panel555.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck555 : ContactPolynomial.check scale ops epsilon panel555.row=true := by decide +kernel
theorem modelCheck556 : panel556.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck556 : ContactPolynomial.check scale ops epsilon panel556.row=true := by decide +kernel
theorem modelCheck557 : panel557.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck557 : ContactPolynomial.check scale ops epsilon panel557.row=true := by decide +kernel
theorem modelCheck558 : panel558.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck558 : ContactPolynomial.check scale ops epsilon panel558.row=true := by decide +kernel
theorem modelCheck559 : panel559.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck559 : ContactPolynomial.check scale ops epsilon panel559.row=true := by decide +kernel
theorem modelCheck560 : panel560.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck560 : ContactPolynomial.check scale ops epsilon panel560.row=true := by decide +kernel
theorem modelCheck561 : panel561.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck561 : ContactPolynomial.check scale ops epsilon panel561.row=true := by decide +kernel
theorem modelCheck562 : panel562.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck562 : ContactPolynomial.check scale ops epsilon panel562.row=true := by decide +kernel
theorem modelCheck563 : panel563.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck563 : ContactPolynomial.check scale ops epsilon panel563.row=true := by decide +kernel
theorem modelCheck564 : panel564.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck564 : ContactPolynomial.check scale ops epsilon panel564.row=true := by decide +kernel
theorem modelCheck565 : panel565.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck565 : ContactPolynomial.check scale ops epsilon panel565.row=true := by decide +kernel
theorem modelCheck566 : panel566.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck566 : ContactPolynomial.check scale ops epsilon panel566.row=true := by decide +kernel
theorem modelCheck567 : panel567.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck567 : ContactPolynomial.check scale ops epsilon panel567.row=true := by decide +kernel
theorem modelCheck568 : panel568.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck568 : ContactPolynomial.check scale ops epsilon panel568.row=true := by decide +kernel
theorem modelCheck569 : panel569.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck569 : ContactPolynomial.check scale ops epsilon panel569.row=true := by decide +kernel
theorem modelCheck570 : panel570.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck570 : ContactPolynomial.check scale ops epsilon panel570.row=true := by decide +kernel
theorem modelCheck571 : panel571.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck571 : ContactPolynomial.check scale ops epsilon panel571.row=true := by decide +kernel
theorem modelCheck572 : panel572.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck572 : ContactPolynomial.check scale ops epsilon panel572.row=true := by decide +kernel
theorem modelCheck573 : panel573.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck573 : ContactPolynomial.check scale ops epsilon panel573.row=true := by decide +kernel
theorem modelCheck574 : panel574.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck574 : ContactPolynomial.check scale ops epsilon panel574.row=true := by decide +kernel
theorem modelCheck575 : panel575.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck575 : ContactPolynomial.check scale ops epsilon panel575.row=true := by decide +kernel
end «2610.05164v2».Certificates.Compact.ContactValues
