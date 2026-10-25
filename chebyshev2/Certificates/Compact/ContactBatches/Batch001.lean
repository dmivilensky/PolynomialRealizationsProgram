import chebyshev2.Certificates.Compact.ContactBatches.Data001

/-!
Article: chebyshev2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 32–63.
Use: `chebyshev2.Certificates.Compact.ContactValues.residualCheck63` feeds
`chebyshev2.Certificates.Compact.ContactValues.valid63` (valid63).
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
theorem modelCheck32 : panel32.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck32 : ContactPolynomial.check scale ops epsilon panel32.row=true := by decide +kernel
theorem modelCheck33 : panel33.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck33 : ContactPolynomial.check scale ops epsilon panel33.row=true := by decide +kernel
theorem modelCheck34 : panel34.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck34 : ContactPolynomial.check scale ops epsilon panel34.row=true := by decide +kernel
theorem modelCheck35 : panel35.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck35 : ContactPolynomial.check scale ops epsilon panel35.row=true := by decide +kernel
theorem modelCheck36 : panel36.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck36 : ContactPolynomial.check scale ops epsilon panel36.row=true := by decide +kernel
theorem modelCheck37 : panel37.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck37 : ContactPolynomial.check scale ops epsilon panel37.row=true := by decide +kernel
theorem modelCheck38 : panel38.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck38 : ContactPolynomial.check scale ops epsilon panel38.row=true := by decide +kernel
theorem modelCheck39 : panel39.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck39 : ContactPolynomial.check scale ops epsilon panel39.row=true := by decide +kernel
theorem modelCheck40 : panel40.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck40 : ContactPolynomial.check scale ops epsilon panel40.row=true := by decide +kernel
theorem modelCheck41 : panel41.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck41 : ContactPolynomial.check scale ops epsilon panel41.row=true := by decide +kernel
theorem modelCheck42 : panel42.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck42 : ContactPolynomial.check scale ops epsilon panel42.row=true := by decide +kernel
theorem modelCheck43 : panel43.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck43 : ContactPolynomial.check scale ops epsilon panel43.row=true := by decide +kernel
theorem modelCheck44 : panel44.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck44 : ContactPolynomial.check scale ops epsilon panel44.row=true := by decide +kernel
theorem modelCheck45 : panel45.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck45 : ContactPolynomial.check scale ops epsilon panel45.row=true := by decide +kernel
theorem modelCheck46 : panel46.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck46 : ContactPolynomial.check scale ops epsilon panel46.row=true := by decide +kernel
theorem modelCheck47 : panel47.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck47 : ContactPolynomial.check scale ops epsilon panel47.row=true := by decide +kernel
theorem modelCheck48 : panel48.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck48 : ContactPolynomial.check scale ops epsilon panel48.row=true := by decide +kernel
theorem modelCheck49 : panel49.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck49 : ContactPolynomial.check scale ops epsilon panel49.row=true := by decide +kernel
theorem modelCheck50 : panel50.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck50 : ContactPolynomial.check scale ops epsilon panel50.row=true := by decide +kernel
theorem modelCheck51 : panel51.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck51 : ContactPolynomial.check scale ops epsilon panel51.row=true := by decide +kernel
theorem modelCheck52 : panel52.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck52 : ContactPolynomial.check scale ops epsilon panel52.row=true := by decide +kernel
theorem modelCheck53 : panel53.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck53 : ContactPolynomial.check scale ops epsilon panel53.row=true := by decide +kernel
theorem modelCheck54 : panel54.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck54 : ContactPolynomial.check scale ops epsilon panel54.row=true := by decide +kernel
theorem modelCheck55 : panel55.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck55 : ContactPolynomial.check scale ops epsilon panel55.row=true := by decide +kernel
theorem modelCheck56 : panel56.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck56 : ContactPolynomial.check scale ops epsilon panel56.row=true := by decide +kernel
theorem modelCheck57 : panel57.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck57 : ContactPolynomial.check scale ops epsilon panel57.row=true := by decide +kernel
theorem modelCheck58 : panel58.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck58 : ContactPolynomial.check scale ops epsilon panel58.row=true := by decide +kernel
theorem modelCheck59 : panel59.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck59 : ContactPolynomial.check scale ops epsilon panel59.row=true := by decide +kernel
theorem modelCheck60 : panel60.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck60 : ContactPolynomial.check scale ops epsilon panel60.row=true := by decide +kernel
theorem modelCheck61 : panel61.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck61 : ContactPolynomial.check scale ops epsilon panel61.row=true := by decide +kernel
theorem modelCheck62 : panel62.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck62 : ContactPolynomial.check scale ops epsilon panel62.row=true := by decide +kernel
theorem modelCheck63 : panel63.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck63 : ContactPolynomial.check scale ops epsilon panel63.row=true := by decide +kernel
end chebyshev2.Certificates.Compact.ContactValues
