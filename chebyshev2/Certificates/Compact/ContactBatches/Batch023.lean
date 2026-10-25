import chebyshev2.Certificates.Compact.ContactBatches.Data023

/-!
Article: chebyshev2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 736–767.
Use: `chebyshev2.Certificates.Compact.ContactValues.residualCheck767` feeds
`chebyshev2.Certificates.Compact.ContactValues.valid767` (valid767).
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
theorem modelCheck736 : panel736.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck736 : ContactPolynomial.check scale ops epsilon panel736.row=true := by decide +kernel
theorem modelCheck737 : panel737.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck737 : ContactPolynomial.check scale ops epsilon panel737.row=true := by decide +kernel
theorem modelCheck738 : panel738.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck738 : ContactPolynomial.check scale ops epsilon panel738.row=true := by decide +kernel
theorem modelCheck739 : panel739.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck739 : ContactPolynomial.check scale ops epsilon panel739.row=true := by decide +kernel
theorem modelCheck740 : panel740.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck740 : ContactPolynomial.check scale ops epsilon panel740.row=true := by decide +kernel
theorem modelCheck741 : panel741.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck741 : ContactPolynomial.check scale ops epsilon panel741.row=true := by decide +kernel
theorem modelCheck742 : panel742.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck742 : ContactPolynomial.check scale ops epsilon panel742.row=true := by decide +kernel
theorem modelCheck743 : panel743.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck743 : ContactPolynomial.check scale ops epsilon panel743.row=true := by decide +kernel
theorem modelCheck744 : panel744.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck744 : ContactPolynomial.check scale ops epsilon panel744.row=true := by decide +kernel
theorem modelCheck745 : panel745.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck745 : ContactPolynomial.check scale ops epsilon panel745.row=true := by decide +kernel
theorem modelCheck746 : panel746.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck746 : ContactPolynomial.check scale ops epsilon panel746.row=true := by decide +kernel
theorem modelCheck747 : panel747.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck747 : ContactPolynomial.check scale ops epsilon panel747.row=true := by decide +kernel
theorem modelCheck748 : panel748.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck748 : ContactPolynomial.check scale ops epsilon panel748.row=true := by decide +kernel
theorem modelCheck749 : panel749.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck749 : ContactPolynomial.check scale ops epsilon panel749.row=true := by decide +kernel
theorem modelCheck750 : panel750.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck750 : ContactPolynomial.check scale ops epsilon panel750.row=true := by decide +kernel
theorem modelCheck751 : panel751.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck751 : ContactPolynomial.check scale ops epsilon panel751.row=true := by decide +kernel
theorem modelCheck752 : panel752.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck752 : ContactPolynomial.check scale ops epsilon panel752.row=true := by decide +kernel
theorem modelCheck753 : panel753.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck753 : ContactPolynomial.check scale ops epsilon panel753.row=true := by decide +kernel
theorem modelCheck754 : panel754.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck754 : ContactPolynomial.check scale ops epsilon panel754.row=true := by decide +kernel
theorem modelCheck755 : panel755.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck755 : ContactPolynomial.check scale ops epsilon panel755.row=true := by decide +kernel
theorem modelCheck756 : panel756.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck756 : ContactPolynomial.check scale ops epsilon panel756.row=true := by decide +kernel
theorem modelCheck757 : panel757.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck757 : ContactPolynomial.check scale ops epsilon panel757.row=true := by decide +kernel
theorem modelCheck758 : panel758.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck758 : ContactPolynomial.check scale ops epsilon panel758.row=true := by decide +kernel
theorem modelCheck759 : panel759.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck759 : ContactPolynomial.check scale ops epsilon panel759.row=true := by decide +kernel
theorem modelCheck760 : panel760.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck760 : ContactPolynomial.check scale ops epsilon panel760.row=true := by decide +kernel
theorem modelCheck761 : panel761.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck761 : ContactPolynomial.check scale ops epsilon panel761.row=true := by decide +kernel
theorem modelCheck762 : panel762.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck762 : ContactPolynomial.check scale ops epsilon panel762.row=true := by decide +kernel
theorem modelCheck763 : panel763.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck763 : ContactPolynomial.check scale ops epsilon panel763.row=true := by decide +kernel
theorem modelCheck764 : panel764.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck764 : ContactPolynomial.check scale ops epsilon panel764.row=true := by decide +kernel
theorem modelCheck765 : panel765.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck765 : ContactPolynomial.check scale ops epsilon panel765.row=true := by decide +kernel
theorem modelCheck766 : panel766.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck766 : ContactPolynomial.check scale ops epsilon panel766.row=true := by decide +kernel
theorem modelCheck767 : panel767.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck767 : ContactPolynomial.check scale ops epsilon panel767.row=true := by decide +kernel
end chebyshev2.Certificates.Compact.ContactValues
