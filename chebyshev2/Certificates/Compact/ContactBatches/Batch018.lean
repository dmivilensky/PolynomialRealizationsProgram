import chebyshev2.Certificates.Compact.ContactBatches.Data018

/-!
Article: chebyshev2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 576–607.
Use: `chebyshev2.Certificates.Compact.ContactValues.residualCheck607` feeds
`chebyshev2.Certificates.Compact.ContactValues.valid607` (valid607).
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
theorem modelCheck576 : panel576.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck576 : ContactPolynomial.check scale ops epsilon panel576.row=true := by decide +kernel
theorem modelCheck577 : panel577.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck577 : ContactPolynomial.check scale ops epsilon panel577.row=true := by decide +kernel
theorem modelCheck578 : panel578.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck578 : ContactPolynomial.check scale ops epsilon panel578.row=true := by decide +kernel
theorem modelCheck579 : panel579.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck579 : ContactPolynomial.check scale ops epsilon panel579.row=true := by decide +kernel
theorem modelCheck580 : panel580.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck580 : ContactPolynomial.check scale ops epsilon panel580.row=true := by decide +kernel
theorem modelCheck581 : panel581.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck581 : ContactPolynomial.check scale ops epsilon panel581.row=true := by decide +kernel
theorem modelCheck582 : panel582.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck582 : ContactPolynomial.check scale ops epsilon panel582.row=true := by decide +kernel
theorem modelCheck583 : panel583.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck583 : ContactPolynomial.check scale ops epsilon panel583.row=true := by decide +kernel
theorem modelCheck584 : panel584.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck584 : ContactPolynomial.check scale ops epsilon panel584.row=true := by decide +kernel
theorem modelCheck585 : panel585.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck585 : ContactPolynomial.check scale ops epsilon panel585.row=true := by decide +kernel
theorem modelCheck586 : panel586.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck586 : ContactPolynomial.check scale ops epsilon panel586.row=true := by decide +kernel
theorem modelCheck587 : panel587.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck587 : ContactPolynomial.check scale ops epsilon panel587.row=true := by decide +kernel
theorem modelCheck588 : panel588.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck588 : ContactPolynomial.check scale ops epsilon panel588.row=true := by decide +kernel
theorem modelCheck589 : panel589.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck589 : ContactPolynomial.check scale ops epsilon panel589.row=true := by decide +kernel
theorem modelCheck590 : panel590.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck590 : ContactPolynomial.check scale ops epsilon panel590.row=true := by decide +kernel
theorem modelCheck591 : panel591.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck591 : ContactPolynomial.check scale ops epsilon panel591.row=true := by decide +kernel
theorem modelCheck592 : panel592.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck592 : ContactPolynomial.check scale ops epsilon panel592.row=true := by decide +kernel
theorem modelCheck593 : panel593.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck593 : ContactPolynomial.check scale ops epsilon panel593.row=true := by decide +kernel
theorem modelCheck594 : panel594.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck594 : ContactPolynomial.check scale ops epsilon panel594.row=true := by decide +kernel
theorem modelCheck595 : panel595.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck595 : ContactPolynomial.check scale ops epsilon panel595.row=true := by decide +kernel
theorem modelCheck596 : panel596.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck596 : ContactPolynomial.check scale ops epsilon panel596.row=true := by decide +kernel
theorem modelCheck597 : panel597.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck597 : ContactPolynomial.check scale ops epsilon panel597.row=true := by decide +kernel
theorem modelCheck598 : panel598.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck598 : ContactPolynomial.check scale ops epsilon panel598.row=true := by decide +kernel
theorem modelCheck599 : panel599.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck599 : ContactPolynomial.check scale ops epsilon panel599.row=true := by decide +kernel
theorem modelCheck600 : panel600.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck600 : ContactPolynomial.check scale ops epsilon panel600.row=true := by decide +kernel
theorem modelCheck601 : panel601.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck601 : ContactPolynomial.check scale ops epsilon panel601.row=true := by decide +kernel
theorem modelCheck602 : panel602.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck602 : ContactPolynomial.check scale ops epsilon panel602.row=true := by decide +kernel
theorem modelCheck603 : panel603.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck603 : ContactPolynomial.check scale ops epsilon panel603.row=true := by decide +kernel
theorem modelCheck604 : panel604.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck604 : ContactPolynomial.check scale ops epsilon panel604.row=true := by decide +kernel
theorem modelCheck605 : panel605.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck605 : ContactPolynomial.check scale ops epsilon panel605.row=true := by decide +kernel
theorem modelCheck606 : panel606.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck606 : ContactPolynomial.check scale ops epsilon panel606.row=true := by decide +kernel
theorem modelCheck607 : panel607.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck607 : ContactPolynomial.check scale ops epsilon panel607.row=true := by decide +kernel
end chebyshev2.Certificates.Compact.ContactValues
