import chebyshev2.Certificates.Compact.ContactBatches.Data000

/-!
Article: chebyshev2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 0–31.
Use: `chebyshev2.Certificates.Compact.ContactValues.residualCheck31` feeds
`chebyshev2.Certificates.Compact.ContactValues.valid31` (valid31).
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
theorem modelCheck0 : panel0.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck0 : ContactPolynomial.check scale ops epsilon panel0.row=true := by decide +kernel
theorem modelCheck1 : panel1.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1 : ContactPolynomial.check scale ops epsilon panel1.row=true := by decide +kernel
theorem modelCheck2 : panel2.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck2 : ContactPolynomial.check scale ops epsilon panel2.row=true := by decide +kernel
theorem modelCheck3 : panel3.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck3 : ContactPolynomial.check scale ops epsilon panel3.row=true := by decide +kernel
theorem modelCheck4 : panel4.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck4 : ContactPolynomial.check scale ops epsilon panel4.row=true := by decide +kernel
theorem modelCheck5 : panel5.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck5 : ContactPolynomial.check scale ops epsilon panel5.row=true := by decide +kernel
theorem modelCheck6 : panel6.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck6 : ContactPolynomial.check scale ops epsilon panel6.row=true := by decide +kernel
theorem modelCheck7 : panel7.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck7 : ContactPolynomial.check scale ops epsilon panel7.row=true := by decide +kernel
theorem modelCheck8 : panel8.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck8 : ContactPolynomial.check scale ops epsilon panel8.row=true := by decide +kernel
theorem modelCheck9 : panel9.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck9 : ContactPolynomial.check scale ops epsilon panel9.row=true := by decide +kernel
theorem modelCheck10 : panel10.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck10 : ContactPolynomial.check scale ops epsilon panel10.row=true := by decide +kernel
theorem modelCheck11 : panel11.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck11 : ContactPolynomial.check scale ops epsilon panel11.row=true := by decide +kernel
theorem modelCheck12 : panel12.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck12 : ContactPolynomial.check scale ops epsilon panel12.row=true := by decide +kernel
theorem modelCheck13 : panel13.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck13 : ContactPolynomial.check scale ops epsilon panel13.row=true := by decide +kernel
theorem modelCheck14 : panel14.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck14 : ContactPolynomial.check scale ops epsilon panel14.row=true := by decide +kernel
theorem modelCheck15 : panel15.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck15 : ContactPolynomial.check scale ops epsilon panel15.row=true := by decide +kernel
theorem modelCheck16 : panel16.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck16 : ContactPolynomial.check scale ops epsilon panel16.row=true := by decide +kernel
theorem modelCheck17 : panel17.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck17 : ContactPolynomial.check scale ops epsilon panel17.row=true := by decide +kernel
theorem modelCheck18 : panel18.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck18 : ContactPolynomial.check scale ops epsilon panel18.row=true := by decide +kernel
theorem modelCheck19 : panel19.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck19 : ContactPolynomial.check scale ops epsilon panel19.row=true := by decide +kernel
theorem modelCheck20 : panel20.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck20 : ContactPolynomial.check scale ops epsilon panel20.row=true := by decide +kernel
theorem modelCheck21 : panel21.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck21 : ContactPolynomial.check scale ops epsilon panel21.row=true := by decide +kernel
theorem modelCheck22 : panel22.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck22 : ContactPolynomial.check scale ops epsilon panel22.row=true := by decide +kernel
theorem modelCheck23 : panel23.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck23 : ContactPolynomial.check scale ops epsilon panel23.row=true := by decide +kernel
theorem modelCheck24 : panel24.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck24 : ContactPolynomial.check scale ops epsilon panel24.row=true := by decide +kernel
theorem modelCheck25 : panel25.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck25 : ContactPolynomial.check scale ops epsilon panel25.row=true := by decide +kernel
theorem modelCheck26 : panel26.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck26 : ContactPolynomial.check scale ops epsilon panel26.row=true := by decide +kernel
theorem modelCheck27 : panel27.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck27 : ContactPolynomial.check scale ops epsilon panel27.row=true := by decide +kernel
theorem modelCheck28 : panel28.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck28 : ContactPolynomial.check scale ops epsilon panel28.row=true := by decide +kernel
theorem modelCheck29 : panel29.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck29 : ContactPolynomial.check scale ops epsilon panel29.row=true := by decide +kernel
theorem modelCheck30 : panel30.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck30 : ContactPolynomial.check scale ops epsilon panel30.row=true := by decide +kernel
theorem modelCheck31 : panel31.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck31 : ContactPolynomial.check scale ops epsilon panel31.row=true := by decide +kernel
end chebyshev2.Certificates.Compact.ContactValues
