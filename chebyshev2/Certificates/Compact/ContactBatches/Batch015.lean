import chebyshev2.Certificates.Compact.ContactBatches.Data015

/-!
Article: chebyshev2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 480–511.
Use: `chebyshev2.Certificates.Compact.ContactValues.residualCheck511` feeds
`chebyshev2.Certificates.Compact.ContactValues.valid511` (valid511).
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
theorem modelCheck480 : panel480.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck480 : ContactPolynomial.check scale ops epsilon panel480.row=true := by decide +kernel
theorem modelCheck481 : panel481.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck481 : ContactPolynomial.check scale ops epsilon panel481.row=true := by decide +kernel
theorem modelCheck482 : panel482.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck482 : ContactPolynomial.check scale ops epsilon panel482.row=true := by decide +kernel
theorem modelCheck483 : panel483.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck483 : ContactPolynomial.check scale ops epsilon panel483.row=true := by decide +kernel
theorem modelCheck484 : panel484.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck484 : ContactPolynomial.check scale ops epsilon panel484.row=true := by decide +kernel
theorem modelCheck485 : panel485.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck485 : ContactPolynomial.check scale ops epsilon panel485.row=true := by decide +kernel
theorem modelCheck486 : panel486.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck486 : ContactPolynomial.check scale ops epsilon panel486.row=true := by decide +kernel
theorem modelCheck487 : panel487.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck487 : ContactPolynomial.check scale ops epsilon panel487.row=true := by decide +kernel
theorem modelCheck488 : panel488.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck488 : ContactPolynomial.check scale ops epsilon panel488.row=true := by decide +kernel
theorem modelCheck489 : panel489.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck489 : ContactPolynomial.check scale ops epsilon panel489.row=true := by decide +kernel
theorem modelCheck490 : panel490.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck490 : ContactPolynomial.check scale ops epsilon panel490.row=true := by decide +kernel
theorem modelCheck491 : panel491.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck491 : ContactPolynomial.check scale ops epsilon panel491.row=true := by decide +kernel
theorem modelCheck492 : panel492.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck492 : ContactPolynomial.check scale ops epsilon panel492.row=true := by decide +kernel
theorem modelCheck493 : panel493.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck493 : ContactPolynomial.check scale ops epsilon panel493.row=true := by decide +kernel
theorem modelCheck494 : panel494.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck494 : ContactPolynomial.check scale ops epsilon panel494.row=true := by decide +kernel
theorem modelCheck495 : panel495.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck495 : ContactPolynomial.check scale ops epsilon panel495.row=true := by decide +kernel
theorem modelCheck496 : panel496.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck496 : ContactPolynomial.check scale ops epsilon panel496.row=true := by decide +kernel
theorem modelCheck497 : panel497.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck497 : ContactPolynomial.check scale ops epsilon panel497.row=true := by decide +kernel
theorem modelCheck498 : panel498.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck498 : ContactPolynomial.check scale ops epsilon panel498.row=true := by decide +kernel
theorem modelCheck499 : panel499.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck499 : ContactPolynomial.check scale ops epsilon panel499.row=true := by decide +kernel
theorem modelCheck500 : panel500.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck500 : ContactPolynomial.check scale ops epsilon panel500.row=true := by decide +kernel
theorem modelCheck501 : panel501.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck501 : ContactPolynomial.check scale ops epsilon panel501.row=true := by decide +kernel
theorem modelCheck502 : panel502.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck502 : ContactPolynomial.check scale ops epsilon panel502.row=true := by decide +kernel
theorem modelCheck503 : panel503.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck503 : ContactPolynomial.check scale ops epsilon panel503.row=true := by decide +kernel
theorem modelCheck504 : panel504.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck504 : ContactPolynomial.check scale ops epsilon panel504.row=true := by decide +kernel
theorem modelCheck505 : panel505.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck505 : ContactPolynomial.check scale ops epsilon panel505.row=true := by decide +kernel
theorem modelCheck506 : panel506.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck506 : ContactPolynomial.check scale ops epsilon panel506.row=true := by decide +kernel
theorem modelCheck507 : panel507.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck507 : ContactPolynomial.check scale ops epsilon panel507.row=true := by decide +kernel
theorem modelCheck508 : panel508.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck508 : ContactPolynomial.check scale ops epsilon panel508.row=true := by decide +kernel
theorem modelCheck509 : panel509.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck509 : ContactPolynomial.check scale ops epsilon panel509.row=true := by decide +kernel
theorem modelCheck510 : panel510.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck510 : ContactPolynomial.check scale ops epsilon panel510.row=true := by decide +kernel
theorem modelCheck511 : panel511.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck511 : ContactPolynomial.check scale ops epsilon panel511.row=true := by decide +kernel
end chebyshev2.Certificates.Compact.ContactValues
