import chebyshev2.Certificates.Compact.AmplitudeBatches.Data001

/-!
Article: chebyshev2, Section 4.1.
Kernel reduction of acceptance for amplitude quadrature panels 32–63.
Use: `chebyshev2.Certificates.Compact.AmplitudeValues.check63` feeds
`chebyshev2.Certificates.Compact.AmplitudeValues.valid63` (valid63).
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
theorem check32 : AmplitudePolynomial.check scale ops epsilon panel32=true := by decide +kernel
theorem check33 : AmplitudePolynomial.check scale ops epsilon panel33=true := by decide +kernel
theorem check34 : AmplitudePolynomial.check scale ops epsilon panel34=true := by decide +kernel
theorem check35 : AmplitudePolynomial.check scale ops epsilon panel35=true := by decide +kernel
theorem check36 : AmplitudePolynomial.check scale ops epsilon panel36=true := by decide +kernel
theorem check37 : AmplitudePolynomial.check scale ops epsilon panel37=true := by decide +kernel
theorem check38 : AmplitudePolynomial.check scale ops epsilon panel38=true := by decide +kernel
theorem check39 : AmplitudePolynomial.check scale ops epsilon panel39=true := by decide +kernel
theorem check40 : AmplitudePolynomial.check scale ops epsilon panel40=true := by decide +kernel
theorem check41 : AmplitudePolynomial.check scale ops epsilon panel41=true := by decide +kernel
theorem check42 : AmplitudePolynomial.check scale ops epsilon panel42=true := by decide +kernel
theorem check43 : AmplitudePolynomial.check scale ops epsilon panel43=true := by decide +kernel
theorem check44 : AmplitudePolynomial.check scale ops epsilon panel44=true := by decide +kernel
theorem check45 : AmplitudePolynomial.check scale ops epsilon panel45=true := by decide +kernel
theorem check46 : AmplitudePolynomial.check scale ops epsilon panel46=true := by decide +kernel
theorem check47 : AmplitudePolynomial.check scale ops epsilon panel47=true := by decide +kernel
theorem check48 : AmplitudePolynomial.check scale ops epsilon panel48=true := by decide +kernel
theorem check49 : AmplitudePolynomial.check scale ops epsilon panel49=true := by decide +kernel
theorem check50 : AmplitudePolynomial.check scale ops epsilon panel50=true := by decide +kernel
theorem check51 : AmplitudePolynomial.check scale ops epsilon panel51=true := by decide +kernel
theorem check52 : AmplitudePolynomial.check scale ops epsilon panel52=true := by decide +kernel
theorem check53 : AmplitudePolynomial.check scale ops epsilon panel53=true := by decide +kernel
theorem check54 : AmplitudePolynomial.check scale ops epsilon panel54=true := by decide +kernel
theorem check55 : AmplitudePolynomial.check scale ops epsilon panel55=true := by decide +kernel
theorem check56 : AmplitudePolynomial.check scale ops epsilon panel56=true := by decide +kernel
theorem check57 : AmplitudePolynomial.check scale ops epsilon panel57=true := by decide +kernel
theorem check58 : AmplitudePolynomial.check scale ops epsilon panel58=true := by decide +kernel
theorem check59 : AmplitudePolynomial.check scale ops epsilon panel59=true := by decide +kernel
theorem check60 : AmplitudePolynomial.check scale ops epsilon panel60=true := by decide +kernel
theorem check61 : AmplitudePolynomial.check scale ops epsilon panel61=true := by decide +kernel
theorem check62 : AmplitudePolynomial.check scale ops epsilon panel62=true := by decide +kernel
theorem check63 : AmplitudePolynomial.check scale ops epsilon panel63=true := by decide +kernel
end chebyshev2.Certificates.Compact.AmplitudeValues
