import chebyshev2.Certificates.Compact.ContactBatches.Data021

/-!
Article: chebyshev2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 672–703.
Use: `chebyshev2.Certificates.Compact.ContactValues.residualCheck703` feeds
`chebyshev2.Certificates.Compact.ContactValues.valid703` (valid703).
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
theorem modelCheck672 : panel672.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck672 : ContactPolynomial.check scale ops epsilon panel672.row=true := by decide +kernel
theorem modelCheck673 : panel673.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck673 : ContactPolynomial.check scale ops epsilon panel673.row=true := by decide +kernel
theorem modelCheck674 : panel674.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck674 : ContactPolynomial.check scale ops epsilon panel674.row=true := by decide +kernel
theorem modelCheck675 : panel675.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck675 : ContactPolynomial.check scale ops epsilon panel675.row=true := by decide +kernel
theorem modelCheck676 : panel676.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck676 : ContactPolynomial.check scale ops epsilon panel676.row=true := by decide +kernel
theorem modelCheck677 : panel677.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck677 : ContactPolynomial.check scale ops epsilon panel677.row=true := by decide +kernel
theorem modelCheck678 : panel678.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck678 : ContactPolynomial.check scale ops epsilon panel678.row=true := by decide +kernel
theorem modelCheck679 : panel679.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck679 : ContactPolynomial.check scale ops epsilon panel679.row=true := by decide +kernel
theorem modelCheck680 : panel680.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck680 : ContactPolynomial.check scale ops epsilon panel680.row=true := by decide +kernel
theorem modelCheck681 : panel681.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck681 : ContactPolynomial.check scale ops epsilon panel681.row=true := by decide +kernel
theorem modelCheck682 : panel682.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck682 : ContactPolynomial.check scale ops epsilon panel682.row=true := by decide +kernel
theorem modelCheck683 : panel683.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck683 : ContactPolynomial.check scale ops epsilon panel683.row=true := by decide +kernel
theorem modelCheck684 : panel684.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck684 : ContactPolynomial.check scale ops epsilon panel684.row=true := by decide +kernel
theorem modelCheck685 : panel685.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck685 : ContactPolynomial.check scale ops epsilon panel685.row=true := by decide +kernel
theorem modelCheck686 : panel686.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck686 : ContactPolynomial.check scale ops epsilon panel686.row=true := by decide +kernel
theorem modelCheck687 : panel687.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck687 : ContactPolynomial.check scale ops epsilon panel687.row=true := by decide +kernel
theorem modelCheck688 : panel688.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck688 : ContactPolynomial.check scale ops epsilon panel688.row=true := by decide +kernel
theorem modelCheck689 : panel689.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck689 : ContactPolynomial.check scale ops epsilon panel689.row=true := by decide +kernel
theorem modelCheck690 : panel690.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck690 : ContactPolynomial.check scale ops epsilon panel690.row=true := by decide +kernel
theorem modelCheck691 : panel691.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck691 : ContactPolynomial.check scale ops epsilon panel691.row=true := by decide +kernel
theorem modelCheck692 : panel692.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck692 : ContactPolynomial.check scale ops epsilon panel692.row=true := by decide +kernel
theorem modelCheck693 : panel693.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck693 : ContactPolynomial.check scale ops epsilon panel693.row=true := by decide +kernel
theorem modelCheck694 : panel694.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck694 : ContactPolynomial.check scale ops epsilon panel694.row=true := by decide +kernel
theorem modelCheck695 : panel695.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck695 : ContactPolynomial.check scale ops epsilon panel695.row=true := by decide +kernel
theorem modelCheck696 : panel696.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck696 : ContactPolynomial.check scale ops epsilon panel696.row=true := by decide +kernel
theorem modelCheck697 : panel697.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck697 : ContactPolynomial.check scale ops epsilon panel697.row=true := by decide +kernel
theorem modelCheck698 : panel698.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck698 : ContactPolynomial.check scale ops epsilon panel698.row=true := by decide +kernel
theorem modelCheck699 : panel699.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck699 : ContactPolynomial.check scale ops epsilon panel699.row=true := by decide +kernel
theorem modelCheck700 : panel700.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck700 : ContactPolynomial.check scale ops epsilon panel700.row=true := by decide +kernel
theorem modelCheck701 : panel701.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck701 : ContactPolynomial.check scale ops epsilon panel701.row=true := by decide +kernel
theorem modelCheck702 : panel702.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck702 : ContactPolynomial.check scale ops epsilon panel702.row=true := by decide +kernel
theorem modelCheck703 : panel703.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck703 : ContactPolynomial.check scale ops epsilon panel703.row=true := by decide +kernel
end chebyshev2.Certificates.Compact.ContactValues
