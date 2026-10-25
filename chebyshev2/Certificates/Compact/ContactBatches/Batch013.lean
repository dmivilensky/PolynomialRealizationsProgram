import chebyshev2.Certificates.Compact.ContactBatches.Data013

/-!
Article: chebyshev2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 416–447.
Use: `chebyshev2.Certificates.Compact.ContactValues.residualCheck447` feeds
`chebyshev2.Certificates.Compact.ContactValues.valid447` (valid447).
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
theorem modelCheck416 : panel416.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck416 : ContactPolynomial.check scale ops epsilon panel416.row=true := by decide +kernel
theorem modelCheck417 : panel417.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck417 : ContactPolynomial.check scale ops epsilon panel417.row=true := by decide +kernel
theorem modelCheck418 : panel418.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck418 : ContactPolynomial.check scale ops epsilon panel418.row=true := by decide +kernel
theorem modelCheck419 : panel419.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck419 : ContactPolynomial.check scale ops epsilon panel419.row=true := by decide +kernel
theorem modelCheck420 : panel420.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck420 : ContactPolynomial.check scale ops epsilon panel420.row=true := by decide +kernel
theorem modelCheck421 : panel421.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck421 : ContactPolynomial.check scale ops epsilon panel421.row=true := by decide +kernel
theorem modelCheck422 : panel422.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck422 : ContactPolynomial.check scale ops epsilon panel422.row=true := by decide +kernel
theorem modelCheck423 : panel423.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck423 : ContactPolynomial.check scale ops epsilon panel423.row=true := by decide +kernel
theorem modelCheck424 : panel424.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck424 : ContactPolynomial.check scale ops epsilon panel424.row=true := by decide +kernel
theorem modelCheck425 : panel425.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck425 : ContactPolynomial.check scale ops epsilon panel425.row=true := by decide +kernel
theorem modelCheck426 : panel426.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck426 : ContactPolynomial.check scale ops epsilon panel426.row=true := by decide +kernel
theorem modelCheck427 : panel427.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck427 : ContactPolynomial.check scale ops epsilon panel427.row=true := by decide +kernel
theorem modelCheck428 : panel428.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck428 : ContactPolynomial.check scale ops epsilon panel428.row=true := by decide +kernel
theorem modelCheck429 : panel429.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck429 : ContactPolynomial.check scale ops epsilon panel429.row=true := by decide +kernel
theorem modelCheck430 : panel430.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck430 : ContactPolynomial.check scale ops epsilon panel430.row=true := by decide +kernel
theorem modelCheck431 : panel431.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck431 : ContactPolynomial.check scale ops epsilon panel431.row=true := by decide +kernel
theorem modelCheck432 : panel432.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck432 : ContactPolynomial.check scale ops epsilon panel432.row=true := by decide +kernel
theorem modelCheck433 : panel433.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck433 : ContactPolynomial.check scale ops epsilon panel433.row=true := by decide +kernel
theorem modelCheck434 : panel434.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck434 : ContactPolynomial.check scale ops epsilon panel434.row=true := by decide +kernel
theorem modelCheck435 : panel435.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck435 : ContactPolynomial.check scale ops epsilon panel435.row=true := by decide +kernel
theorem modelCheck436 : panel436.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck436 : ContactPolynomial.check scale ops epsilon panel436.row=true := by decide +kernel
theorem modelCheck437 : panel437.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck437 : ContactPolynomial.check scale ops epsilon panel437.row=true := by decide +kernel
theorem modelCheck438 : panel438.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck438 : ContactPolynomial.check scale ops epsilon panel438.row=true := by decide +kernel
theorem modelCheck439 : panel439.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck439 : ContactPolynomial.check scale ops epsilon panel439.row=true := by decide +kernel
theorem modelCheck440 : panel440.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck440 : ContactPolynomial.check scale ops epsilon panel440.row=true := by decide +kernel
theorem modelCheck441 : panel441.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck441 : ContactPolynomial.check scale ops epsilon panel441.row=true := by decide +kernel
theorem modelCheck442 : panel442.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck442 : ContactPolynomial.check scale ops epsilon panel442.row=true := by decide +kernel
theorem modelCheck443 : panel443.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck443 : ContactPolynomial.check scale ops epsilon panel443.row=true := by decide +kernel
theorem modelCheck444 : panel444.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck444 : ContactPolynomial.check scale ops epsilon panel444.row=true := by decide +kernel
theorem modelCheck445 : panel445.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck445 : ContactPolynomial.check scale ops epsilon panel445.row=true := by decide +kernel
theorem modelCheck446 : panel446.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck446 : ContactPolynomial.check scale ops epsilon panel446.row=true := by decide +kernel
theorem modelCheck447 : panel447.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck447 : ContactPolynomial.check scale ops epsilon panel447.row=true := by decide +kernel
end chebyshev2.Certificates.Compact.ContactValues
