import «2610.05164v2».Certificates.Compact.ContactBatches.Data029

/-!
Article: 2610.05164v2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 928–959.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.residualCheck959` feeds
`«2610.05164v2».Certificates.Compact.ContactValues.valid959` (valid959).
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
theorem modelCheck928 : panel928.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck928 : ContactPolynomial.check scale ops epsilon panel928.row=true := by decide +kernel
theorem modelCheck929 : panel929.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck929 : ContactPolynomial.check scale ops epsilon panel929.row=true := by decide +kernel
theorem modelCheck930 : panel930.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck930 : ContactPolynomial.check scale ops epsilon panel930.row=true := by decide +kernel
theorem modelCheck931 : panel931.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck931 : ContactPolynomial.check scale ops epsilon panel931.row=true := by decide +kernel
theorem modelCheck932 : panel932.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck932 : ContactPolynomial.check scale ops epsilon panel932.row=true := by decide +kernel
theorem modelCheck933 : panel933.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck933 : ContactPolynomial.check scale ops epsilon panel933.row=true := by decide +kernel
theorem modelCheck934 : panel934.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck934 : ContactPolynomial.check scale ops epsilon panel934.row=true := by decide +kernel
theorem modelCheck935 : panel935.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck935 : ContactPolynomial.check scale ops epsilon panel935.row=true := by decide +kernel
theorem modelCheck936 : panel936.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck936 : ContactPolynomial.check scale ops epsilon panel936.row=true := by decide +kernel
theorem modelCheck937 : panel937.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck937 : ContactPolynomial.check scale ops epsilon panel937.row=true := by decide +kernel
theorem modelCheck938 : panel938.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck938 : ContactPolynomial.check scale ops epsilon panel938.row=true := by decide +kernel
theorem modelCheck939 : panel939.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck939 : ContactPolynomial.check scale ops epsilon panel939.row=true := by decide +kernel
theorem modelCheck940 : panel940.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck940 : ContactPolynomial.check scale ops epsilon panel940.row=true := by decide +kernel
theorem modelCheck941 : panel941.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck941 : ContactPolynomial.check scale ops epsilon panel941.row=true := by decide +kernel
theorem modelCheck942 : panel942.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck942 : ContactPolynomial.check scale ops epsilon panel942.row=true := by decide +kernel
theorem modelCheck943 : panel943.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck943 : ContactPolynomial.check scale ops epsilon panel943.row=true := by decide +kernel
theorem modelCheck944 : panel944.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck944 : ContactPolynomial.check scale ops epsilon panel944.row=true := by decide +kernel
theorem modelCheck945 : panel945.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck945 : ContactPolynomial.check scale ops epsilon panel945.row=true := by decide +kernel
theorem modelCheck946 : panel946.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck946 : ContactPolynomial.check scale ops epsilon panel946.row=true := by decide +kernel
theorem modelCheck947 : panel947.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck947 : ContactPolynomial.check scale ops epsilon panel947.row=true := by decide +kernel
theorem modelCheck948 : panel948.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck948 : ContactPolynomial.check scale ops epsilon panel948.row=true := by decide +kernel
theorem modelCheck949 : panel949.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck949 : ContactPolynomial.check scale ops epsilon panel949.row=true := by decide +kernel
theorem modelCheck950 : panel950.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck950 : ContactPolynomial.check scale ops epsilon panel950.row=true := by decide +kernel
theorem modelCheck951 : panel951.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck951 : ContactPolynomial.check scale ops epsilon panel951.row=true := by decide +kernel
theorem modelCheck952 : panel952.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck952 : ContactPolynomial.check scale ops epsilon panel952.row=true := by decide +kernel
theorem modelCheck953 : panel953.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck953 : ContactPolynomial.check scale ops epsilon panel953.row=true := by decide +kernel
theorem modelCheck954 : panel954.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck954 : ContactPolynomial.check scale ops epsilon panel954.row=true := by decide +kernel
theorem modelCheck955 : panel955.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck955 : ContactPolynomial.check scale ops epsilon panel955.row=true := by decide +kernel
theorem modelCheck956 : panel956.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck956 : ContactPolynomial.check scale ops epsilon panel956.row=true := by decide +kernel
theorem modelCheck957 : panel957.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck957 : ContactPolynomial.check scale ops epsilon panel957.row=true := by decide +kernel
theorem modelCheck958 : panel958.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck958 : ContactPolynomial.check scale ops epsilon panel958.row=true := by decide +kernel
theorem modelCheck959 : panel959.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck959 : ContactPolynomial.check scale ops epsilon panel959.row=true := by decide +kernel
end «2610.05164v2».Certificates.Compact.ContactValues
