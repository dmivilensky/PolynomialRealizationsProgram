import chebyshev2.Certificates.Compact.ContactBatches.Data024

/-!
Article: chebyshev2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 768–799.
Use: `chebyshev2.Certificates.Compact.ContactValues.residualCheck799` feeds
`chebyshev2.Certificates.Compact.ContactValues.valid799` (valid799).
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
theorem modelCheck768 : panel768.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck768 : ContactPolynomial.check scale ops epsilon panel768.row=true := by decide +kernel
theorem modelCheck769 : panel769.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck769 : ContactPolynomial.check scale ops epsilon panel769.row=true := by decide +kernel
theorem modelCheck770 : panel770.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck770 : ContactPolynomial.check scale ops epsilon panel770.row=true := by decide +kernel
theorem modelCheck771 : panel771.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck771 : ContactPolynomial.check scale ops epsilon panel771.row=true := by decide +kernel
theorem modelCheck772 : panel772.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck772 : ContactPolynomial.check scale ops epsilon panel772.row=true := by decide +kernel
theorem modelCheck773 : panel773.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck773 : ContactPolynomial.check scale ops epsilon panel773.row=true := by decide +kernel
theorem modelCheck774 : panel774.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck774 : ContactPolynomial.check scale ops epsilon panel774.row=true := by decide +kernel
theorem modelCheck775 : panel775.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck775 : ContactPolynomial.check scale ops epsilon panel775.row=true := by decide +kernel
theorem modelCheck776 : panel776.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck776 : ContactPolynomial.check scale ops epsilon panel776.row=true := by decide +kernel
theorem modelCheck777 : panel777.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck777 : ContactPolynomial.check scale ops epsilon panel777.row=true := by decide +kernel
theorem modelCheck778 : panel778.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck778 : ContactPolynomial.check scale ops epsilon panel778.row=true := by decide +kernel
theorem modelCheck779 : panel779.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck779 : ContactPolynomial.check scale ops epsilon panel779.row=true := by decide +kernel
theorem modelCheck780 : panel780.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck780 : ContactPolynomial.check scale ops epsilon panel780.row=true := by decide +kernel
theorem modelCheck781 : panel781.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck781 : ContactPolynomial.check scale ops epsilon panel781.row=true := by decide +kernel
theorem modelCheck782 : panel782.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck782 : ContactPolynomial.check scale ops epsilon panel782.row=true := by decide +kernel
theorem modelCheck783 : panel783.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck783 : ContactPolynomial.check scale ops epsilon panel783.row=true := by decide +kernel
theorem modelCheck784 : panel784.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck784 : ContactPolynomial.check scale ops epsilon panel784.row=true := by decide +kernel
theorem modelCheck785 : panel785.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck785 : ContactPolynomial.check scale ops epsilon panel785.row=true := by decide +kernel
theorem modelCheck786 : panel786.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck786 : ContactPolynomial.check scale ops epsilon panel786.row=true := by decide +kernel
theorem modelCheck787 : panel787.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck787 : ContactPolynomial.check scale ops epsilon panel787.row=true := by decide +kernel
theorem modelCheck788 : panel788.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck788 : ContactPolynomial.check scale ops epsilon panel788.row=true := by decide +kernel
theorem modelCheck789 : panel789.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck789 : ContactPolynomial.check scale ops epsilon panel789.row=true := by decide +kernel
theorem modelCheck790 : panel790.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck790 : ContactPolynomial.check scale ops epsilon panel790.row=true := by decide +kernel
theorem modelCheck791 : panel791.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck791 : ContactPolynomial.check scale ops epsilon panel791.row=true := by decide +kernel
theorem modelCheck792 : panel792.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck792 : ContactPolynomial.check scale ops epsilon panel792.row=true := by decide +kernel
theorem modelCheck793 : panel793.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck793 : ContactPolynomial.check scale ops epsilon panel793.row=true := by decide +kernel
theorem modelCheck794 : panel794.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck794 : ContactPolynomial.check scale ops epsilon panel794.row=true := by decide +kernel
theorem modelCheck795 : panel795.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck795 : ContactPolynomial.check scale ops epsilon panel795.row=true := by decide +kernel
theorem modelCheck796 : panel796.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck796 : ContactPolynomial.check scale ops epsilon panel796.row=true := by decide +kernel
theorem modelCheck797 : panel797.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck797 : ContactPolynomial.check scale ops epsilon panel797.row=true := by decide +kernel
theorem modelCheck798 : panel798.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck798 : ContactPolynomial.check scale ops epsilon panel798.row=true := by decide +kernel
theorem modelCheck799 : panel799.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck799 : ContactPolynomial.check scale ops epsilon panel799.row=true := by decide +kernel
end chebyshev2.Certificates.Compact.ContactValues
