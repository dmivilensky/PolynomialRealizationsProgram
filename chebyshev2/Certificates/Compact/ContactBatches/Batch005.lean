import chebyshev2.Certificates.Compact.ContactBatches.Data005

/-!
Article: chebyshev2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 160–191.
Use: `chebyshev2.Certificates.Compact.ContactValues.residualCheck191` feeds
`chebyshev2.Certificates.Compact.ContactValues.valid191` (valid191).
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
theorem modelCheck160 : panel160.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck160 : ContactPolynomial.check scale ops epsilon panel160.row=true := by decide +kernel
theorem modelCheck161 : panel161.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck161 : ContactPolynomial.check scale ops epsilon panel161.row=true := by decide +kernel
theorem modelCheck162 : panel162.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck162 : ContactPolynomial.check scale ops epsilon panel162.row=true := by decide +kernel
theorem modelCheck163 : panel163.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck163 : ContactPolynomial.check scale ops epsilon panel163.row=true := by decide +kernel
theorem modelCheck164 : panel164.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck164 : ContactPolynomial.check scale ops epsilon panel164.row=true := by decide +kernel
theorem modelCheck165 : panel165.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck165 : ContactPolynomial.check scale ops epsilon panel165.row=true := by decide +kernel
theorem modelCheck166 : panel166.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck166 : ContactPolynomial.check scale ops epsilon panel166.row=true := by decide +kernel
theorem modelCheck167 : panel167.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck167 : ContactPolynomial.check scale ops epsilon panel167.row=true := by decide +kernel
theorem modelCheck168 : panel168.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck168 : ContactPolynomial.check scale ops epsilon panel168.row=true := by decide +kernel
theorem modelCheck169 : panel169.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck169 : ContactPolynomial.check scale ops epsilon panel169.row=true := by decide +kernel
theorem modelCheck170 : panel170.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck170 : ContactPolynomial.check scale ops epsilon panel170.row=true := by decide +kernel
theorem modelCheck171 : panel171.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck171 : ContactPolynomial.check scale ops epsilon panel171.row=true := by decide +kernel
theorem modelCheck172 : panel172.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck172 : ContactPolynomial.check scale ops epsilon panel172.row=true := by decide +kernel
theorem modelCheck173 : panel173.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck173 : ContactPolynomial.check scale ops epsilon panel173.row=true := by decide +kernel
theorem modelCheck174 : panel174.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck174 : ContactPolynomial.check scale ops epsilon panel174.row=true := by decide +kernel
theorem modelCheck175 : panel175.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck175 : ContactPolynomial.check scale ops epsilon panel175.row=true := by decide +kernel
theorem modelCheck176 : panel176.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck176 : ContactPolynomial.check scale ops epsilon panel176.row=true := by decide +kernel
theorem modelCheck177 : panel177.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck177 : ContactPolynomial.check scale ops epsilon panel177.row=true := by decide +kernel
theorem modelCheck178 : panel178.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck178 : ContactPolynomial.check scale ops epsilon panel178.row=true := by decide +kernel
theorem modelCheck179 : panel179.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck179 : ContactPolynomial.check scale ops epsilon panel179.row=true := by decide +kernel
theorem modelCheck180 : panel180.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck180 : ContactPolynomial.check scale ops epsilon panel180.row=true := by decide +kernel
theorem modelCheck181 : panel181.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck181 : ContactPolynomial.check scale ops epsilon panel181.row=true := by decide +kernel
theorem modelCheck182 : panel182.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck182 : ContactPolynomial.check scale ops epsilon panel182.row=true := by decide +kernel
theorem modelCheck183 : panel183.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck183 : ContactPolynomial.check scale ops epsilon panel183.row=true := by decide +kernel
theorem modelCheck184 : panel184.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck184 : ContactPolynomial.check scale ops epsilon panel184.row=true := by decide +kernel
theorem modelCheck185 : panel185.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck185 : ContactPolynomial.check scale ops epsilon panel185.row=true := by decide +kernel
theorem modelCheck186 : panel186.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck186 : ContactPolynomial.check scale ops epsilon panel186.row=true := by decide +kernel
theorem modelCheck187 : panel187.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck187 : ContactPolynomial.check scale ops epsilon panel187.row=true := by decide +kernel
theorem modelCheck188 : panel188.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck188 : ContactPolynomial.check scale ops epsilon panel188.row=true := by decide +kernel
theorem modelCheck189 : panel189.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck189 : ContactPolynomial.check scale ops epsilon panel189.row=true := by decide +kernel
theorem modelCheck190 : panel190.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck190 : ContactPolynomial.check scale ops epsilon panel190.row=true := by decide +kernel
theorem modelCheck191 : panel191.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck191 : ContactPolynomial.check scale ops epsilon panel191.row=true := by decide +kernel
end chebyshev2.Certificates.Compact.ContactValues
