import chebyshev2.Certificates.Compact.ContactBatches.Data034

/-!
Article: chebyshev2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 1088–1119.
Use: `chebyshev2.Certificates.Compact.ContactValues.residualCheck1119` feeds
`chebyshev2.Certificates.Compact.ContactValues.valid1119` (valid1119).
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
theorem modelCheck1088 : panel1088.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1088 : ContactPolynomial.check scale ops epsilon panel1088.row=true := by decide +kernel
theorem modelCheck1089 : panel1089.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1089 : ContactPolynomial.check scale ops epsilon panel1089.row=true := by decide +kernel
theorem modelCheck1090 : panel1090.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1090 : ContactPolynomial.check scale ops epsilon panel1090.row=true := by decide +kernel
theorem modelCheck1091 : panel1091.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1091 : ContactPolynomial.check scale ops epsilon panel1091.row=true := by decide +kernel
theorem modelCheck1092 : panel1092.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1092 : ContactPolynomial.check scale ops epsilon panel1092.row=true := by decide +kernel
theorem modelCheck1093 : panel1093.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1093 : ContactPolynomial.check scale ops epsilon panel1093.row=true := by decide +kernel
theorem modelCheck1094 : panel1094.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1094 : ContactPolynomial.check scale ops epsilon panel1094.row=true := by decide +kernel
theorem modelCheck1095 : panel1095.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1095 : ContactPolynomial.check scale ops epsilon panel1095.row=true := by decide +kernel
theorem modelCheck1096 : panel1096.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1096 : ContactPolynomial.check scale ops epsilon panel1096.row=true := by decide +kernel
theorem modelCheck1097 : panel1097.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1097 : ContactPolynomial.check scale ops epsilon panel1097.row=true := by decide +kernel
theorem modelCheck1098 : panel1098.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1098 : ContactPolynomial.check scale ops epsilon panel1098.row=true := by decide +kernel
theorem modelCheck1099 : panel1099.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1099 : ContactPolynomial.check scale ops epsilon panel1099.row=true := by decide +kernel
theorem modelCheck1100 : panel1100.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1100 : ContactPolynomial.check scale ops epsilon panel1100.row=true := by decide +kernel
theorem modelCheck1101 : panel1101.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1101 : ContactPolynomial.check scale ops epsilon panel1101.row=true := by decide +kernel
theorem modelCheck1102 : panel1102.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1102 : ContactPolynomial.check scale ops epsilon panel1102.row=true := by decide +kernel
theorem modelCheck1103 : panel1103.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1103 : ContactPolynomial.check scale ops epsilon panel1103.row=true := by decide +kernel
theorem modelCheck1104 : panel1104.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1104 : ContactPolynomial.check scale ops epsilon panel1104.row=true := by decide +kernel
theorem modelCheck1105 : panel1105.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1105 : ContactPolynomial.check scale ops epsilon panel1105.row=true := by decide +kernel
theorem modelCheck1106 : panel1106.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1106 : ContactPolynomial.check scale ops epsilon panel1106.row=true := by decide +kernel
theorem modelCheck1107 : panel1107.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1107 : ContactPolynomial.check scale ops epsilon panel1107.row=true := by decide +kernel
theorem modelCheck1108 : panel1108.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1108 : ContactPolynomial.check scale ops epsilon panel1108.row=true := by decide +kernel
theorem modelCheck1109 : panel1109.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1109 : ContactPolynomial.check scale ops epsilon panel1109.row=true := by decide +kernel
theorem modelCheck1110 : panel1110.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1110 : ContactPolynomial.check scale ops epsilon panel1110.row=true := by decide +kernel
theorem modelCheck1111 : panel1111.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1111 : ContactPolynomial.check scale ops epsilon panel1111.row=true := by decide +kernel
theorem modelCheck1112 : panel1112.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1112 : ContactPolynomial.check scale ops epsilon panel1112.row=true := by decide +kernel
theorem modelCheck1113 : panel1113.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1113 : ContactPolynomial.check scale ops epsilon panel1113.row=true := by decide +kernel
theorem modelCheck1114 : panel1114.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1114 : ContactPolynomial.check scale ops epsilon panel1114.row=true := by decide +kernel
theorem modelCheck1115 : panel1115.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1115 : ContactPolynomial.check scale ops epsilon panel1115.row=true := by decide +kernel
theorem modelCheck1116 : panel1116.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1116 : ContactPolynomial.check scale ops epsilon panel1116.row=true := by decide +kernel
theorem modelCheck1117 : panel1117.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1117 : ContactPolynomial.check scale ops epsilon panel1117.row=true := by decide +kernel
theorem modelCheck1118 : panel1118.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1118 : ContactPolynomial.check scale ops epsilon panel1118.row=true := by decide +kernel
theorem modelCheck1119 : panel1119.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1119 : ContactPolynomial.check scale ops epsilon panel1119.row=true := by decide +kernel
end chebyshev2.Certificates.Compact.ContactValues
