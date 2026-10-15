import «2610.05164v2».Certificates.Compact.ContactBatches.Data006

/-!
Article: 2610.05164v2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 192–223.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.residualCheck223` feeds
`«2610.05164v2».Certificates.Compact.ContactValues.valid223` (valid223).
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
theorem modelCheck192 : panel192.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck192 : ContactPolynomial.check scale ops epsilon panel192.row=true := by decide +kernel
theorem modelCheck193 : panel193.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck193 : ContactPolynomial.check scale ops epsilon panel193.row=true := by decide +kernel
theorem modelCheck194 : panel194.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck194 : ContactPolynomial.check scale ops epsilon panel194.row=true := by decide +kernel
theorem modelCheck195 : panel195.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck195 : ContactPolynomial.check scale ops epsilon panel195.row=true := by decide +kernel
theorem modelCheck196 : panel196.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck196 : ContactPolynomial.check scale ops epsilon panel196.row=true := by decide +kernel
theorem modelCheck197 : panel197.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck197 : ContactPolynomial.check scale ops epsilon panel197.row=true := by decide +kernel
theorem modelCheck198 : panel198.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck198 : ContactPolynomial.check scale ops epsilon panel198.row=true := by decide +kernel
theorem modelCheck199 : panel199.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck199 : ContactPolynomial.check scale ops epsilon panel199.row=true := by decide +kernel
theorem modelCheck200 : panel200.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck200 : ContactPolynomial.check scale ops epsilon panel200.row=true := by decide +kernel
theorem modelCheck201 : panel201.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck201 : ContactPolynomial.check scale ops epsilon panel201.row=true := by decide +kernel
theorem modelCheck202 : panel202.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck202 : ContactPolynomial.check scale ops epsilon panel202.row=true := by decide +kernel
theorem modelCheck203 : panel203.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck203 : ContactPolynomial.check scale ops epsilon panel203.row=true := by decide +kernel
theorem modelCheck204 : panel204.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck204 : ContactPolynomial.check scale ops epsilon panel204.row=true := by decide +kernel
theorem modelCheck205 : panel205.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck205 : ContactPolynomial.check scale ops epsilon panel205.row=true := by decide +kernel
theorem modelCheck206 : panel206.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck206 : ContactPolynomial.check scale ops epsilon panel206.row=true := by decide +kernel
theorem modelCheck207 : panel207.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck207 : ContactPolynomial.check scale ops epsilon panel207.row=true := by decide +kernel
theorem modelCheck208 : panel208.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck208 : ContactPolynomial.check scale ops epsilon panel208.row=true := by decide +kernel
theorem modelCheck209 : panel209.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck209 : ContactPolynomial.check scale ops epsilon panel209.row=true := by decide +kernel
theorem modelCheck210 : panel210.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck210 : ContactPolynomial.check scale ops epsilon panel210.row=true := by decide +kernel
theorem modelCheck211 : panel211.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck211 : ContactPolynomial.check scale ops epsilon panel211.row=true := by decide +kernel
theorem modelCheck212 : panel212.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck212 : ContactPolynomial.check scale ops epsilon panel212.row=true := by decide +kernel
theorem modelCheck213 : panel213.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck213 : ContactPolynomial.check scale ops epsilon panel213.row=true := by decide +kernel
theorem modelCheck214 : panel214.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck214 : ContactPolynomial.check scale ops epsilon panel214.row=true := by decide +kernel
theorem modelCheck215 : panel215.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck215 : ContactPolynomial.check scale ops epsilon panel215.row=true := by decide +kernel
theorem modelCheck216 : panel216.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck216 : ContactPolynomial.check scale ops epsilon panel216.row=true := by decide +kernel
theorem modelCheck217 : panel217.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck217 : ContactPolynomial.check scale ops epsilon panel217.row=true := by decide +kernel
theorem modelCheck218 : panel218.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck218 : ContactPolynomial.check scale ops epsilon panel218.row=true := by decide +kernel
theorem modelCheck219 : panel219.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck219 : ContactPolynomial.check scale ops epsilon panel219.row=true := by decide +kernel
theorem modelCheck220 : panel220.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck220 : ContactPolynomial.check scale ops epsilon panel220.row=true := by decide +kernel
theorem modelCheck221 : panel221.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck221 : ContactPolynomial.check scale ops epsilon panel221.row=true := by decide +kernel
theorem modelCheck222 : panel222.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck222 : ContactPolynomial.check scale ops epsilon panel222.row=true := by decide +kernel
theorem modelCheck223 : panel223.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck223 : ContactPolynomial.check scale ops epsilon panel223.row=true := by decide +kernel
end «2610.05164v2».Certificates.Compact.ContactValues
