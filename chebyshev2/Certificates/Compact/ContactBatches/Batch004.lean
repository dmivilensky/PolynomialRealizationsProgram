import chebyshev2.Certificates.Compact.ContactBatches.Data004

/-!
Article: chebyshev2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 128–159.
Use: `chebyshev2.Certificates.Compact.ContactValues.residualCheck159` feeds
`chebyshev2.Certificates.Compact.ContactValues.valid159` (valid159).
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
theorem modelCheck128 : panel128.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck128 : ContactPolynomial.check scale ops epsilon panel128.row=true := by decide +kernel
theorem modelCheck129 : panel129.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck129 : ContactPolynomial.check scale ops epsilon panel129.row=true := by decide +kernel
theorem modelCheck130 : panel130.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck130 : ContactPolynomial.check scale ops epsilon panel130.row=true := by decide +kernel
theorem modelCheck131 : panel131.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck131 : ContactPolynomial.check scale ops epsilon panel131.row=true := by decide +kernel
theorem modelCheck132 : panel132.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck132 : ContactPolynomial.check scale ops epsilon panel132.row=true := by decide +kernel
theorem modelCheck133 : panel133.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck133 : ContactPolynomial.check scale ops epsilon panel133.row=true := by decide +kernel
theorem modelCheck134 : panel134.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck134 : ContactPolynomial.check scale ops epsilon panel134.row=true := by decide +kernel
theorem modelCheck135 : panel135.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck135 : ContactPolynomial.check scale ops epsilon panel135.row=true := by decide +kernel
theorem modelCheck136 : panel136.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck136 : ContactPolynomial.check scale ops epsilon panel136.row=true := by decide +kernel
theorem modelCheck137 : panel137.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck137 : ContactPolynomial.check scale ops epsilon panel137.row=true := by decide +kernel
theorem modelCheck138 : panel138.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck138 : ContactPolynomial.check scale ops epsilon panel138.row=true := by decide +kernel
theorem modelCheck139 : panel139.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck139 : ContactPolynomial.check scale ops epsilon panel139.row=true := by decide +kernel
theorem modelCheck140 : panel140.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck140 : ContactPolynomial.check scale ops epsilon panel140.row=true := by decide +kernel
theorem modelCheck141 : panel141.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck141 : ContactPolynomial.check scale ops epsilon panel141.row=true := by decide +kernel
theorem modelCheck142 : panel142.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck142 : ContactPolynomial.check scale ops epsilon panel142.row=true := by decide +kernel
theorem modelCheck143 : panel143.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck143 : ContactPolynomial.check scale ops epsilon panel143.row=true := by decide +kernel
theorem modelCheck144 : panel144.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck144 : ContactPolynomial.check scale ops epsilon panel144.row=true := by decide +kernel
theorem modelCheck145 : panel145.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck145 : ContactPolynomial.check scale ops epsilon panel145.row=true := by decide +kernel
theorem modelCheck146 : panel146.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck146 : ContactPolynomial.check scale ops epsilon panel146.row=true := by decide +kernel
theorem modelCheck147 : panel147.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck147 : ContactPolynomial.check scale ops epsilon panel147.row=true := by decide +kernel
theorem modelCheck148 : panel148.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck148 : ContactPolynomial.check scale ops epsilon panel148.row=true := by decide +kernel
theorem modelCheck149 : panel149.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck149 : ContactPolynomial.check scale ops epsilon panel149.row=true := by decide +kernel
theorem modelCheck150 : panel150.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck150 : ContactPolynomial.check scale ops epsilon panel150.row=true := by decide +kernel
theorem modelCheck151 : panel151.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck151 : ContactPolynomial.check scale ops epsilon panel151.row=true := by decide +kernel
theorem modelCheck152 : panel152.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck152 : ContactPolynomial.check scale ops epsilon panel152.row=true := by decide +kernel
theorem modelCheck153 : panel153.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck153 : ContactPolynomial.check scale ops epsilon panel153.row=true := by decide +kernel
theorem modelCheck154 : panel154.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck154 : ContactPolynomial.check scale ops epsilon panel154.row=true := by decide +kernel
theorem modelCheck155 : panel155.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck155 : ContactPolynomial.check scale ops epsilon panel155.row=true := by decide +kernel
theorem modelCheck156 : panel156.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck156 : ContactPolynomial.check scale ops epsilon panel156.row=true := by decide +kernel
theorem modelCheck157 : panel157.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck157 : ContactPolynomial.check scale ops epsilon panel157.row=true := by decide +kernel
theorem modelCheck158 : panel158.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck158 : ContactPolynomial.check scale ops epsilon panel158.row=true := by decide +kernel
theorem modelCheck159 : panel159.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck159 : ContactPolynomial.check scale ops epsilon panel159.row=true := by decide +kernel
end chebyshev2.Certificates.Compact.ContactValues
