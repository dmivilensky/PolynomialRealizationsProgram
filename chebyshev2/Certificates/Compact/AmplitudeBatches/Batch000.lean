import chebyshev2.Certificates.Compact.AmplitudeBatches.Data000

/-!
Article: chebyshev2, Section 4.1.
Kernel reduction of acceptance for amplitude quadrature panels 0–31.
Use: `chebyshev2.Certificates.Compact.AmplitudeValues.check31` feeds
`chebyshev2.Certificates.Compact.AmplitudeValues.valid31` (valid31).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace chebyshev2.Certificates.Compact.AmplitudeValues
open chebyshev2.Numerics chebyshev2.Numerics.IntegerCertificate
theorem check0 : AmplitudePolynomial.check scale ops epsilon panel0=true := by decide +kernel
theorem check1 : AmplitudePolynomial.check scale ops epsilon panel1=true := by decide +kernel
theorem check2 : AmplitudePolynomial.check scale ops epsilon panel2=true := by decide +kernel
theorem check3 : AmplitudePolynomial.check scale ops epsilon panel3=true := by decide +kernel
theorem check4 : AmplitudePolynomial.check scale ops epsilon panel4=true := by decide +kernel
theorem check5 : AmplitudePolynomial.check scale ops epsilon panel5=true := by decide +kernel
theorem check6 : AmplitudePolynomial.check scale ops epsilon panel6=true := by decide +kernel
theorem check7 : AmplitudePolynomial.check scale ops epsilon panel7=true := by decide +kernel
theorem check8 : AmplitudePolynomial.check scale ops epsilon panel8=true := by decide +kernel
theorem check9 : AmplitudePolynomial.check scale ops epsilon panel9=true := by decide +kernel
theorem check10 : AmplitudePolynomial.check scale ops epsilon panel10=true := by decide +kernel
theorem check11 : AmplitudePolynomial.check scale ops epsilon panel11=true := by decide +kernel
theorem check12 : AmplitudePolynomial.check scale ops epsilon panel12=true := by decide +kernel
theorem check13 : AmplitudePolynomial.check scale ops epsilon panel13=true := by decide +kernel
theorem check14 : AmplitudePolynomial.check scale ops epsilon panel14=true := by decide +kernel
theorem check15 : AmplitudePolynomial.check scale ops epsilon panel15=true := by decide +kernel
theorem check16 : AmplitudePolynomial.check scale ops epsilon panel16=true := by decide +kernel
theorem check17 : AmplitudePolynomial.check scale ops epsilon panel17=true := by decide +kernel
theorem check18 : AmplitudePolynomial.check scale ops epsilon panel18=true := by decide +kernel
theorem check19 : AmplitudePolynomial.check scale ops epsilon panel19=true := by decide +kernel
theorem check20 : AmplitudePolynomial.check scale ops epsilon panel20=true := by decide +kernel
theorem check21 : AmplitudePolynomial.check scale ops epsilon panel21=true := by decide +kernel
theorem check22 : AmplitudePolynomial.check scale ops epsilon panel22=true := by decide +kernel
theorem check23 : AmplitudePolynomial.check scale ops epsilon panel23=true := by decide +kernel
theorem check24 : AmplitudePolynomial.check scale ops epsilon panel24=true := by decide +kernel
theorem check25 : AmplitudePolynomial.check scale ops epsilon panel25=true := by decide +kernel
theorem check26 : AmplitudePolynomial.check scale ops epsilon panel26=true := by decide +kernel
theorem check27 : AmplitudePolynomial.check scale ops epsilon panel27=true := by decide +kernel
theorem check28 : AmplitudePolynomial.check scale ops epsilon panel28=true := by decide +kernel
theorem check29 : AmplitudePolynomial.check scale ops epsilon panel29=true := by decide +kernel
theorem check30 : AmplitudePolynomial.check scale ops epsilon panel30=true := by decide +kernel
theorem check31 : AmplitudePolynomial.check scale ops epsilon panel31=true := by decide +kernel
end chebyshev2.Certificates.Compact.AmplitudeValues
