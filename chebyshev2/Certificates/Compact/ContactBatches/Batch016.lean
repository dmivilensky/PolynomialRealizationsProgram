import chebyshev2.Certificates.Compact.ContactBatches.Data016

/-!
Article: chebyshev2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 512–543.
Use: `chebyshev2.Certificates.Compact.ContactValues.residualCheck543` feeds
`chebyshev2.Certificates.Compact.ContactValues.valid543` (valid543).
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
theorem modelCheck512 : panel512.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck512 : ContactPolynomial.check scale ops epsilon panel512.row=true := by decide +kernel
theorem modelCheck513 : panel513.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck513 : ContactPolynomial.check scale ops epsilon panel513.row=true := by decide +kernel
theorem modelCheck514 : panel514.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck514 : ContactPolynomial.check scale ops epsilon panel514.row=true := by decide +kernel
theorem modelCheck515 : panel515.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck515 : ContactPolynomial.check scale ops epsilon panel515.row=true := by decide +kernel
theorem modelCheck516 : panel516.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck516 : ContactPolynomial.check scale ops epsilon panel516.row=true := by decide +kernel
theorem modelCheck517 : panel517.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck517 : ContactPolynomial.check scale ops epsilon panel517.row=true := by decide +kernel
theorem modelCheck518 : panel518.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck518 : ContactPolynomial.check scale ops epsilon panel518.row=true := by decide +kernel
theorem modelCheck519 : panel519.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck519 : ContactPolynomial.check scale ops epsilon panel519.row=true := by decide +kernel
theorem modelCheck520 : panel520.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck520 : ContactPolynomial.check scale ops epsilon panel520.row=true := by decide +kernel
theorem modelCheck521 : panel521.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck521 : ContactPolynomial.check scale ops epsilon panel521.row=true := by decide +kernel
theorem modelCheck522 : panel522.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck522 : ContactPolynomial.check scale ops epsilon panel522.row=true := by decide +kernel
theorem modelCheck523 : panel523.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck523 : ContactPolynomial.check scale ops epsilon panel523.row=true := by decide +kernel
theorem modelCheck524 : panel524.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck524 : ContactPolynomial.check scale ops epsilon panel524.row=true := by decide +kernel
theorem modelCheck525 : panel525.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck525 : ContactPolynomial.check scale ops epsilon panel525.row=true := by decide +kernel
theorem modelCheck526 : panel526.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck526 : ContactPolynomial.check scale ops epsilon panel526.row=true := by decide +kernel
theorem modelCheck527 : panel527.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck527 : ContactPolynomial.check scale ops epsilon panel527.row=true := by decide +kernel
theorem modelCheck528 : panel528.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck528 : ContactPolynomial.check scale ops epsilon panel528.row=true := by decide +kernel
theorem modelCheck529 : panel529.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck529 : ContactPolynomial.check scale ops epsilon panel529.row=true := by decide +kernel
theorem modelCheck530 : panel530.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck530 : ContactPolynomial.check scale ops epsilon panel530.row=true := by decide +kernel
theorem modelCheck531 : panel531.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck531 : ContactPolynomial.check scale ops epsilon panel531.row=true := by decide +kernel
theorem modelCheck532 : panel532.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck532 : ContactPolynomial.check scale ops epsilon panel532.row=true := by decide +kernel
theorem modelCheck533 : panel533.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck533 : ContactPolynomial.check scale ops epsilon panel533.row=true := by decide +kernel
theorem modelCheck534 : panel534.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck534 : ContactPolynomial.check scale ops epsilon panel534.row=true := by decide +kernel
theorem modelCheck535 : panel535.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck535 : ContactPolynomial.check scale ops epsilon panel535.row=true := by decide +kernel
theorem modelCheck536 : panel536.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck536 : ContactPolynomial.check scale ops epsilon panel536.row=true := by decide +kernel
theorem modelCheck537 : panel537.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck537 : ContactPolynomial.check scale ops epsilon panel537.row=true := by decide +kernel
theorem modelCheck538 : panel538.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck538 : ContactPolynomial.check scale ops epsilon panel538.row=true := by decide +kernel
theorem modelCheck539 : panel539.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck539 : ContactPolynomial.check scale ops epsilon panel539.row=true := by decide +kernel
theorem modelCheck540 : panel540.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck540 : ContactPolynomial.check scale ops epsilon panel540.row=true := by decide +kernel
theorem modelCheck541 : panel541.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck541 : ContactPolynomial.check scale ops epsilon panel541.row=true := by decide +kernel
theorem modelCheck542 : panel542.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck542 : ContactPolynomial.check scale ops epsilon panel542.row=true := by decide +kernel
theorem modelCheck543 : panel543.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck543 : ContactPolynomial.check scale ops epsilon panel543.row=true := by decide +kernel
end chebyshev2.Certificates.Compact.ContactValues
