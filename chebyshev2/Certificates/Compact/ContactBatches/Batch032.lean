import chebyshev2.Certificates.Compact.ContactBatches.Data032

/-!
Article: chebyshev2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 1024–1055.
Use: `chebyshev2.Certificates.Compact.ContactValues.residualCheck1055` feeds
`chebyshev2.Certificates.Compact.ContactValues.valid1055` (valid1055).
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
theorem modelCheck1024 : panel1024.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1024 : ContactPolynomial.check scale ops epsilon panel1024.row=true := by decide +kernel
theorem modelCheck1025 : panel1025.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1025 : ContactPolynomial.check scale ops epsilon panel1025.row=true := by decide +kernel
theorem modelCheck1026 : panel1026.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1026 : ContactPolynomial.check scale ops epsilon panel1026.row=true := by decide +kernel
theorem modelCheck1027 : panel1027.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1027 : ContactPolynomial.check scale ops epsilon panel1027.row=true := by decide +kernel
theorem modelCheck1028 : panel1028.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1028 : ContactPolynomial.check scale ops epsilon panel1028.row=true := by decide +kernel
theorem modelCheck1029 : panel1029.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1029 : ContactPolynomial.check scale ops epsilon panel1029.row=true := by decide +kernel
theorem modelCheck1030 : panel1030.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1030 : ContactPolynomial.check scale ops epsilon panel1030.row=true := by decide +kernel
theorem modelCheck1031 : panel1031.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1031 : ContactPolynomial.check scale ops epsilon panel1031.row=true := by decide +kernel
theorem modelCheck1032 : panel1032.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1032 : ContactPolynomial.check scale ops epsilon panel1032.row=true := by decide +kernel
theorem modelCheck1033 : panel1033.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1033 : ContactPolynomial.check scale ops epsilon panel1033.row=true := by decide +kernel
theorem modelCheck1034 : panel1034.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1034 : ContactPolynomial.check scale ops epsilon panel1034.row=true := by decide +kernel
theorem modelCheck1035 : panel1035.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1035 : ContactPolynomial.check scale ops epsilon panel1035.row=true := by decide +kernel
theorem modelCheck1036 : panel1036.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1036 : ContactPolynomial.check scale ops epsilon panel1036.row=true := by decide +kernel
theorem modelCheck1037 : panel1037.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1037 : ContactPolynomial.check scale ops epsilon panel1037.row=true := by decide +kernel
theorem modelCheck1038 : panel1038.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1038 : ContactPolynomial.check scale ops epsilon panel1038.row=true := by decide +kernel
theorem modelCheck1039 : panel1039.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1039 : ContactPolynomial.check scale ops epsilon panel1039.row=true := by decide +kernel
theorem modelCheck1040 : panel1040.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1040 : ContactPolynomial.check scale ops epsilon panel1040.row=true := by decide +kernel
theorem modelCheck1041 : panel1041.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1041 : ContactPolynomial.check scale ops epsilon panel1041.row=true := by decide +kernel
theorem modelCheck1042 : panel1042.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1042 : ContactPolynomial.check scale ops epsilon panel1042.row=true := by decide +kernel
theorem modelCheck1043 : panel1043.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1043 : ContactPolynomial.check scale ops epsilon panel1043.row=true := by decide +kernel
theorem modelCheck1044 : panel1044.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1044 : ContactPolynomial.check scale ops epsilon panel1044.row=true := by decide +kernel
theorem modelCheck1045 : panel1045.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1045 : ContactPolynomial.check scale ops epsilon panel1045.row=true := by decide +kernel
theorem modelCheck1046 : panel1046.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1046 : ContactPolynomial.check scale ops epsilon panel1046.row=true := by decide +kernel
theorem modelCheck1047 : panel1047.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1047 : ContactPolynomial.check scale ops epsilon panel1047.row=true := by decide +kernel
theorem modelCheck1048 : panel1048.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1048 : ContactPolynomial.check scale ops epsilon panel1048.row=true := by decide +kernel
theorem modelCheck1049 : panel1049.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1049 : ContactPolynomial.check scale ops epsilon panel1049.row=true := by decide +kernel
theorem modelCheck1050 : panel1050.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1050 : ContactPolynomial.check scale ops epsilon panel1050.row=true := by decide +kernel
theorem modelCheck1051 : panel1051.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1051 : ContactPolynomial.check scale ops epsilon panel1051.row=true := by decide +kernel
theorem modelCheck1052 : panel1052.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1052 : ContactPolynomial.check scale ops epsilon panel1052.row=true := by decide +kernel
theorem modelCheck1053 : panel1053.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1053 : ContactPolynomial.check scale ops epsilon panel1053.row=true := by decide +kernel
theorem modelCheck1054 : panel1054.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1054 : ContactPolynomial.check scale ops epsilon panel1054.row=true := by decide +kernel
theorem modelCheck1055 : panel1055.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1055 : ContactPolynomial.check scale ops epsilon panel1055.row=true := by decide +kernel
end chebyshev2.Certificates.Compact.ContactValues
