import chebyshev2.Certificates.Compact.ContactBatches.Data019

/-!
Article: chebyshev2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 608–639.
Use: `chebyshev2.Certificates.Compact.ContactValues.residualCheck639` feeds
`chebyshev2.Certificates.Compact.ContactValues.valid639` (valid639).
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
theorem modelCheck608 : panel608.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck608 : ContactPolynomial.check scale ops epsilon panel608.row=true := by decide +kernel
theorem modelCheck609 : panel609.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck609 : ContactPolynomial.check scale ops epsilon panel609.row=true := by decide +kernel
theorem modelCheck610 : panel610.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck610 : ContactPolynomial.check scale ops epsilon panel610.row=true := by decide +kernel
theorem modelCheck611 : panel611.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck611 : ContactPolynomial.check scale ops epsilon panel611.row=true := by decide +kernel
theorem modelCheck612 : panel612.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck612 : ContactPolynomial.check scale ops epsilon panel612.row=true := by decide +kernel
theorem modelCheck613 : panel613.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck613 : ContactPolynomial.check scale ops epsilon panel613.row=true := by decide +kernel
theorem modelCheck614 : panel614.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck614 : ContactPolynomial.check scale ops epsilon panel614.row=true := by decide +kernel
theorem modelCheck615 : panel615.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck615 : ContactPolynomial.check scale ops epsilon panel615.row=true := by decide +kernel
theorem modelCheck616 : panel616.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck616 : ContactPolynomial.check scale ops epsilon panel616.row=true := by decide +kernel
theorem modelCheck617 : panel617.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck617 : ContactPolynomial.check scale ops epsilon panel617.row=true := by decide +kernel
theorem modelCheck618 : panel618.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck618 : ContactPolynomial.check scale ops epsilon panel618.row=true := by decide +kernel
theorem modelCheck619 : panel619.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck619 : ContactPolynomial.check scale ops epsilon panel619.row=true := by decide +kernel
theorem modelCheck620 : panel620.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck620 : ContactPolynomial.check scale ops epsilon panel620.row=true := by decide +kernel
theorem modelCheck621 : panel621.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck621 : ContactPolynomial.check scale ops epsilon panel621.row=true := by decide +kernel
theorem modelCheck622 : panel622.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck622 : ContactPolynomial.check scale ops epsilon panel622.row=true := by decide +kernel
theorem modelCheck623 : panel623.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck623 : ContactPolynomial.check scale ops epsilon panel623.row=true := by decide +kernel
theorem modelCheck624 : panel624.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck624 : ContactPolynomial.check scale ops epsilon panel624.row=true := by decide +kernel
theorem modelCheck625 : panel625.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck625 : ContactPolynomial.check scale ops epsilon panel625.row=true := by decide +kernel
theorem modelCheck626 : panel626.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck626 : ContactPolynomial.check scale ops epsilon panel626.row=true := by decide +kernel
theorem modelCheck627 : panel627.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck627 : ContactPolynomial.check scale ops epsilon panel627.row=true := by decide +kernel
theorem modelCheck628 : panel628.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck628 : ContactPolynomial.check scale ops epsilon panel628.row=true := by decide +kernel
theorem modelCheck629 : panel629.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck629 : ContactPolynomial.check scale ops epsilon panel629.row=true := by decide +kernel
theorem modelCheck630 : panel630.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck630 : ContactPolynomial.check scale ops epsilon panel630.row=true := by decide +kernel
theorem modelCheck631 : panel631.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck631 : ContactPolynomial.check scale ops epsilon panel631.row=true := by decide +kernel
theorem modelCheck632 : panel632.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck632 : ContactPolynomial.check scale ops epsilon panel632.row=true := by decide +kernel
theorem modelCheck633 : panel633.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck633 : ContactPolynomial.check scale ops epsilon panel633.row=true := by decide +kernel
theorem modelCheck634 : panel634.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck634 : ContactPolynomial.check scale ops epsilon panel634.row=true := by decide +kernel
theorem modelCheck635 : panel635.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck635 : ContactPolynomial.check scale ops epsilon panel635.row=true := by decide +kernel
theorem modelCheck636 : panel636.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck636 : ContactPolynomial.check scale ops epsilon panel636.row=true := by decide +kernel
theorem modelCheck637 : panel637.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck637 : ContactPolynomial.check scale ops epsilon panel637.row=true := by decide +kernel
theorem modelCheck638 : panel638.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck638 : ContactPolynomial.check scale ops epsilon panel638.row=true := by decide +kernel
theorem modelCheck639 : panel639.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck639 : ContactPolynomial.check scale ops epsilon panel639.row=true := by decide +kernel
end chebyshev2.Certificates.Compact.ContactValues
