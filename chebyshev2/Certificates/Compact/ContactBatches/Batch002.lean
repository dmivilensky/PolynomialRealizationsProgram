import chebyshev2.Certificates.Compact.ContactBatches.Data002

/-!
Article: chebyshev2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 64–95.
Use: `chebyshev2.Certificates.Compact.ContactValues.residualCheck95` feeds
`chebyshev2.Certificates.Compact.ContactValues.valid95` (valid95).
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
theorem modelCheck64 : panel64.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck64 : ContactPolynomial.check scale ops epsilon panel64.row=true := by decide +kernel
theorem modelCheck65 : panel65.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck65 : ContactPolynomial.check scale ops epsilon panel65.row=true := by decide +kernel
theorem modelCheck66 : panel66.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck66 : ContactPolynomial.check scale ops epsilon panel66.row=true := by decide +kernel
theorem modelCheck67 : panel67.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck67 : ContactPolynomial.check scale ops epsilon panel67.row=true := by decide +kernel
theorem modelCheck68 : panel68.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck68 : ContactPolynomial.check scale ops epsilon panel68.row=true := by decide +kernel
theorem modelCheck69 : panel69.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck69 : ContactPolynomial.check scale ops epsilon panel69.row=true := by decide +kernel
theorem modelCheck70 : panel70.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck70 : ContactPolynomial.check scale ops epsilon panel70.row=true := by decide +kernel
theorem modelCheck71 : panel71.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck71 : ContactPolynomial.check scale ops epsilon panel71.row=true := by decide +kernel
theorem modelCheck72 : panel72.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck72 : ContactPolynomial.check scale ops epsilon panel72.row=true := by decide +kernel
theorem modelCheck73 : panel73.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck73 : ContactPolynomial.check scale ops epsilon panel73.row=true := by decide +kernel
theorem modelCheck74 : panel74.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck74 : ContactPolynomial.check scale ops epsilon panel74.row=true := by decide +kernel
theorem modelCheck75 : panel75.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck75 : ContactPolynomial.check scale ops epsilon panel75.row=true := by decide +kernel
theorem modelCheck76 : panel76.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck76 : ContactPolynomial.check scale ops epsilon panel76.row=true := by decide +kernel
theorem modelCheck77 : panel77.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck77 : ContactPolynomial.check scale ops epsilon panel77.row=true := by decide +kernel
theorem modelCheck78 : panel78.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck78 : ContactPolynomial.check scale ops epsilon panel78.row=true := by decide +kernel
theorem modelCheck79 : panel79.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck79 : ContactPolynomial.check scale ops epsilon panel79.row=true := by decide +kernel
theorem modelCheck80 : panel80.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck80 : ContactPolynomial.check scale ops epsilon panel80.row=true := by decide +kernel
theorem modelCheck81 : panel81.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck81 : ContactPolynomial.check scale ops epsilon panel81.row=true := by decide +kernel
theorem modelCheck82 : panel82.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck82 : ContactPolynomial.check scale ops epsilon panel82.row=true := by decide +kernel
theorem modelCheck83 : panel83.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck83 : ContactPolynomial.check scale ops epsilon panel83.row=true := by decide +kernel
theorem modelCheck84 : panel84.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck84 : ContactPolynomial.check scale ops epsilon panel84.row=true := by decide +kernel
theorem modelCheck85 : panel85.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck85 : ContactPolynomial.check scale ops epsilon panel85.row=true := by decide +kernel
theorem modelCheck86 : panel86.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck86 : ContactPolynomial.check scale ops epsilon panel86.row=true := by decide +kernel
theorem modelCheck87 : panel87.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck87 : ContactPolynomial.check scale ops epsilon panel87.row=true := by decide +kernel
theorem modelCheck88 : panel88.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck88 : ContactPolynomial.check scale ops epsilon panel88.row=true := by decide +kernel
theorem modelCheck89 : panel89.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck89 : ContactPolynomial.check scale ops epsilon panel89.row=true := by decide +kernel
theorem modelCheck90 : panel90.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck90 : ContactPolynomial.check scale ops epsilon panel90.row=true := by decide +kernel
theorem modelCheck91 : panel91.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck91 : ContactPolynomial.check scale ops epsilon panel91.row=true := by decide +kernel
theorem modelCheck92 : panel92.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck92 : ContactPolynomial.check scale ops epsilon panel92.row=true := by decide +kernel
theorem modelCheck93 : panel93.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck93 : ContactPolynomial.check scale ops epsilon panel93.row=true := by decide +kernel
theorem modelCheck94 : panel94.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck94 : ContactPolynomial.check scale ops epsilon panel94.row=true := by decide +kernel
theorem modelCheck95 : panel95.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck95 : ContactPolynomial.check scale ops epsilon panel95.row=true := by decide +kernel
end chebyshev2.Certificates.Compact.ContactValues
