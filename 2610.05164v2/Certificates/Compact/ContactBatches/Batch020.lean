import «2610.05164v2».Certificates.Compact.ContactBatches.Data020

/-!
Article: 2610.05164v2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 640–671.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.residualCheck671` feeds
`«2610.05164v2».Certificates.Compact.ContactValues.valid671` (valid671).
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
theorem modelCheck640 : panel640.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck640 : ContactPolynomial.check scale ops epsilon panel640.row=true := by decide +kernel
theorem modelCheck641 : panel641.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck641 : ContactPolynomial.check scale ops epsilon panel641.row=true := by decide +kernel
theorem modelCheck642 : panel642.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck642 : ContactPolynomial.check scale ops epsilon panel642.row=true := by decide +kernel
theorem modelCheck643 : panel643.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck643 : ContactPolynomial.check scale ops epsilon panel643.row=true := by decide +kernel
theorem modelCheck644 : panel644.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck644 : ContactPolynomial.check scale ops epsilon panel644.row=true := by decide +kernel
theorem modelCheck645 : panel645.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck645 : ContactPolynomial.check scale ops epsilon panel645.row=true := by decide +kernel
theorem modelCheck646 : panel646.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck646 : ContactPolynomial.check scale ops epsilon panel646.row=true := by decide +kernel
theorem modelCheck647 : panel647.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck647 : ContactPolynomial.check scale ops epsilon panel647.row=true := by decide +kernel
theorem modelCheck648 : panel648.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck648 : ContactPolynomial.check scale ops epsilon panel648.row=true := by decide +kernel
theorem modelCheck649 : panel649.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck649 : ContactPolynomial.check scale ops epsilon panel649.row=true := by decide +kernel
theorem modelCheck650 : panel650.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck650 : ContactPolynomial.check scale ops epsilon panel650.row=true := by decide +kernel
theorem modelCheck651 : panel651.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck651 : ContactPolynomial.check scale ops epsilon panel651.row=true := by decide +kernel
theorem modelCheck652 : panel652.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck652 : ContactPolynomial.check scale ops epsilon panel652.row=true := by decide +kernel
theorem modelCheck653 : panel653.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck653 : ContactPolynomial.check scale ops epsilon panel653.row=true := by decide +kernel
theorem modelCheck654 : panel654.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck654 : ContactPolynomial.check scale ops epsilon panel654.row=true := by decide +kernel
theorem modelCheck655 : panel655.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck655 : ContactPolynomial.check scale ops epsilon panel655.row=true := by decide +kernel
theorem modelCheck656 : panel656.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck656 : ContactPolynomial.check scale ops epsilon panel656.row=true := by decide +kernel
theorem modelCheck657 : panel657.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck657 : ContactPolynomial.check scale ops epsilon panel657.row=true := by decide +kernel
theorem modelCheck658 : panel658.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck658 : ContactPolynomial.check scale ops epsilon panel658.row=true := by decide +kernel
theorem modelCheck659 : panel659.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck659 : ContactPolynomial.check scale ops epsilon panel659.row=true := by decide +kernel
theorem modelCheck660 : panel660.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck660 : ContactPolynomial.check scale ops epsilon panel660.row=true := by decide +kernel
theorem modelCheck661 : panel661.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck661 : ContactPolynomial.check scale ops epsilon panel661.row=true := by decide +kernel
theorem modelCheck662 : panel662.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck662 : ContactPolynomial.check scale ops epsilon panel662.row=true := by decide +kernel
theorem modelCheck663 : panel663.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck663 : ContactPolynomial.check scale ops epsilon panel663.row=true := by decide +kernel
theorem modelCheck664 : panel664.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck664 : ContactPolynomial.check scale ops epsilon panel664.row=true := by decide +kernel
theorem modelCheck665 : panel665.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck665 : ContactPolynomial.check scale ops epsilon panel665.row=true := by decide +kernel
theorem modelCheck666 : panel666.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck666 : ContactPolynomial.check scale ops epsilon panel666.row=true := by decide +kernel
theorem modelCheck667 : panel667.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck667 : ContactPolynomial.check scale ops epsilon panel667.row=true := by decide +kernel
theorem modelCheck668 : panel668.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck668 : ContactPolynomial.check scale ops epsilon panel668.row=true := by decide +kernel
theorem modelCheck669 : panel669.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck669 : ContactPolynomial.check scale ops epsilon panel669.row=true := by decide +kernel
theorem modelCheck670 : panel670.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck670 : ContactPolynomial.check scale ops epsilon panel670.row=true := by decide +kernel
theorem modelCheck671 : panel671.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck671 : ContactPolynomial.check scale ops epsilon panel671.row=true := by decide +kernel
end «2610.05164v2».Certificates.Compact.ContactValues
