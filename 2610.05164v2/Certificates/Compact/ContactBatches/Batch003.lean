import «2610.05164v2».Certificates.Compact.ContactBatches.Data003

/-!
Article: 2610.05164v2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 96–127.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.residualCheck127` feeds
`«2610.05164v2».Certificates.Compact.ContactValues.valid127` (valid127).
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
theorem modelCheck96 : panel96.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck96 : ContactPolynomial.check scale ops epsilon panel96.row=true := by decide +kernel
theorem modelCheck97 : panel97.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck97 : ContactPolynomial.check scale ops epsilon panel97.row=true := by decide +kernel
theorem modelCheck98 : panel98.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck98 : ContactPolynomial.check scale ops epsilon panel98.row=true := by decide +kernel
theorem modelCheck99 : panel99.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck99 : ContactPolynomial.check scale ops epsilon panel99.row=true := by decide +kernel
theorem modelCheck100 : panel100.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck100 : ContactPolynomial.check scale ops epsilon panel100.row=true := by decide +kernel
theorem modelCheck101 : panel101.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck101 : ContactPolynomial.check scale ops epsilon panel101.row=true := by decide +kernel
theorem modelCheck102 : panel102.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck102 : ContactPolynomial.check scale ops epsilon panel102.row=true := by decide +kernel
theorem modelCheck103 : panel103.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck103 : ContactPolynomial.check scale ops epsilon panel103.row=true := by decide +kernel
theorem modelCheck104 : panel104.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck104 : ContactPolynomial.check scale ops epsilon panel104.row=true := by decide +kernel
theorem modelCheck105 : panel105.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck105 : ContactPolynomial.check scale ops epsilon panel105.row=true := by decide +kernel
theorem modelCheck106 : panel106.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck106 : ContactPolynomial.check scale ops epsilon panel106.row=true := by decide +kernel
theorem modelCheck107 : panel107.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck107 : ContactPolynomial.check scale ops epsilon panel107.row=true := by decide +kernel
theorem modelCheck108 : panel108.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck108 : ContactPolynomial.check scale ops epsilon panel108.row=true := by decide +kernel
theorem modelCheck109 : panel109.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck109 : ContactPolynomial.check scale ops epsilon panel109.row=true := by decide +kernel
theorem modelCheck110 : panel110.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck110 : ContactPolynomial.check scale ops epsilon panel110.row=true := by decide +kernel
theorem modelCheck111 : panel111.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck111 : ContactPolynomial.check scale ops epsilon panel111.row=true := by decide +kernel
theorem modelCheck112 : panel112.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck112 : ContactPolynomial.check scale ops epsilon panel112.row=true := by decide +kernel
theorem modelCheck113 : panel113.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck113 : ContactPolynomial.check scale ops epsilon panel113.row=true := by decide +kernel
theorem modelCheck114 : panel114.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck114 : ContactPolynomial.check scale ops epsilon panel114.row=true := by decide +kernel
theorem modelCheck115 : panel115.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck115 : ContactPolynomial.check scale ops epsilon panel115.row=true := by decide +kernel
theorem modelCheck116 : panel116.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck116 : ContactPolynomial.check scale ops epsilon panel116.row=true := by decide +kernel
theorem modelCheck117 : panel117.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck117 : ContactPolynomial.check scale ops epsilon panel117.row=true := by decide +kernel
theorem modelCheck118 : panel118.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck118 : ContactPolynomial.check scale ops epsilon panel118.row=true := by decide +kernel
theorem modelCheck119 : panel119.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck119 : ContactPolynomial.check scale ops epsilon panel119.row=true := by decide +kernel
theorem modelCheck120 : panel120.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck120 : ContactPolynomial.check scale ops epsilon panel120.row=true := by decide +kernel
theorem modelCheck121 : panel121.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck121 : ContactPolynomial.check scale ops epsilon panel121.row=true := by decide +kernel
theorem modelCheck122 : panel122.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck122 : ContactPolynomial.check scale ops epsilon panel122.row=true := by decide +kernel
theorem modelCheck123 : panel123.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck123 : ContactPolynomial.check scale ops epsilon panel123.row=true := by decide +kernel
theorem modelCheck124 : panel124.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck124 : ContactPolynomial.check scale ops epsilon panel124.row=true := by decide +kernel
theorem modelCheck125 : panel125.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck125 : ContactPolynomial.check scale ops epsilon panel125.row=true := by decide +kernel
theorem modelCheck126 : panel126.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck126 : ContactPolynomial.check scale ops epsilon panel126.row=true := by decide +kernel
theorem modelCheck127 : panel127.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck127 : ContactPolynomial.check scale ops epsilon panel127.row=true := by decide +kernel
end «2610.05164v2».Certificates.Compact.ContactValues
