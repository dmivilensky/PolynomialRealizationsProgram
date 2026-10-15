import «2610.05164v2».Certificates.Compact.ContactBatches.Data028

/-!
Article: 2610.05164v2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 896–927.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.residualCheck927` feeds
`«2610.05164v2».Certificates.Compact.ContactValues.valid927` (valid927).
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
theorem modelCheck896 : panel896.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck896 : ContactPolynomial.check scale ops epsilon panel896.row=true := by decide +kernel
theorem modelCheck897 : panel897.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck897 : ContactPolynomial.check scale ops epsilon panel897.row=true := by decide +kernel
theorem modelCheck898 : panel898.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck898 : ContactPolynomial.check scale ops epsilon panel898.row=true := by decide +kernel
theorem modelCheck899 : panel899.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck899 : ContactPolynomial.check scale ops epsilon panel899.row=true := by decide +kernel
theorem modelCheck900 : panel900.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck900 : ContactPolynomial.check scale ops epsilon panel900.row=true := by decide +kernel
theorem modelCheck901 : panel901.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck901 : ContactPolynomial.check scale ops epsilon panel901.row=true := by decide +kernel
theorem modelCheck902 : panel902.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck902 : ContactPolynomial.check scale ops epsilon panel902.row=true := by decide +kernel
theorem modelCheck903 : panel903.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck903 : ContactPolynomial.check scale ops epsilon panel903.row=true := by decide +kernel
theorem modelCheck904 : panel904.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck904 : ContactPolynomial.check scale ops epsilon panel904.row=true := by decide +kernel
theorem modelCheck905 : panel905.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck905 : ContactPolynomial.check scale ops epsilon panel905.row=true := by decide +kernel
theorem modelCheck906 : panel906.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck906 : ContactPolynomial.check scale ops epsilon panel906.row=true := by decide +kernel
theorem modelCheck907 : panel907.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck907 : ContactPolynomial.check scale ops epsilon panel907.row=true := by decide +kernel
theorem modelCheck908 : panel908.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck908 : ContactPolynomial.check scale ops epsilon panel908.row=true := by decide +kernel
theorem modelCheck909 : panel909.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck909 : ContactPolynomial.check scale ops epsilon panel909.row=true := by decide +kernel
theorem modelCheck910 : panel910.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck910 : ContactPolynomial.check scale ops epsilon panel910.row=true := by decide +kernel
theorem modelCheck911 : panel911.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck911 : ContactPolynomial.check scale ops epsilon panel911.row=true := by decide +kernel
theorem modelCheck912 : panel912.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck912 : ContactPolynomial.check scale ops epsilon panel912.row=true := by decide +kernel
theorem modelCheck913 : panel913.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck913 : ContactPolynomial.check scale ops epsilon panel913.row=true := by decide +kernel
theorem modelCheck914 : panel914.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck914 : ContactPolynomial.check scale ops epsilon panel914.row=true := by decide +kernel
theorem modelCheck915 : panel915.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck915 : ContactPolynomial.check scale ops epsilon panel915.row=true := by decide +kernel
theorem modelCheck916 : panel916.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck916 : ContactPolynomial.check scale ops epsilon panel916.row=true := by decide +kernel
theorem modelCheck917 : panel917.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck917 : ContactPolynomial.check scale ops epsilon panel917.row=true := by decide +kernel
theorem modelCheck918 : panel918.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck918 : ContactPolynomial.check scale ops epsilon panel918.row=true := by decide +kernel
theorem modelCheck919 : panel919.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck919 : ContactPolynomial.check scale ops epsilon panel919.row=true := by decide +kernel
theorem modelCheck920 : panel920.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck920 : ContactPolynomial.check scale ops epsilon panel920.row=true := by decide +kernel
theorem modelCheck921 : panel921.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck921 : ContactPolynomial.check scale ops epsilon panel921.row=true := by decide +kernel
theorem modelCheck922 : panel922.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck922 : ContactPolynomial.check scale ops epsilon panel922.row=true := by decide +kernel
theorem modelCheck923 : panel923.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck923 : ContactPolynomial.check scale ops epsilon panel923.row=true := by decide +kernel
theorem modelCheck924 : panel924.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck924 : ContactPolynomial.check scale ops epsilon panel924.row=true := by decide +kernel
theorem modelCheck925 : panel925.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck925 : ContactPolynomial.check scale ops epsilon panel925.row=true := by decide +kernel
theorem modelCheck926 : panel926.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck926 : ContactPolynomial.check scale ops epsilon panel926.row=true := by decide +kernel
theorem modelCheck927 : panel927.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck927 : ContactPolynomial.check scale ops epsilon panel927.row=true := by decide +kernel
end «2610.05164v2».Certificates.Compact.ContactValues
