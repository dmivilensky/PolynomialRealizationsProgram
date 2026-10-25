import chebyshev2.Certificates.Compact.ContactBatches.Data035

/-!
Article: chebyshev2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 1120–1151.
Use: `chebyshev2.Certificates.Compact.ContactValues.residualCheck1151` feeds
`chebyshev2.Certificates.Compact.ContactValues.valid1151` (valid1151).
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
theorem modelCheck1120 : panel1120.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1120 : ContactPolynomial.check scale ops epsilon panel1120.row=true := by decide +kernel
theorem modelCheck1121 : panel1121.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1121 : ContactPolynomial.check scale ops epsilon panel1121.row=true := by decide +kernel
theorem modelCheck1122 : panel1122.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1122 : ContactPolynomial.check scale ops epsilon panel1122.row=true := by decide +kernel
theorem modelCheck1123 : panel1123.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1123 : ContactPolynomial.check scale ops epsilon panel1123.row=true := by decide +kernel
theorem modelCheck1124 : panel1124.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1124 : ContactPolynomial.check scale ops epsilon panel1124.row=true := by decide +kernel
theorem modelCheck1125 : panel1125.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1125 : ContactPolynomial.check scale ops epsilon panel1125.row=true := by decide +kernel
theorem modelCheck1126 : panel1126.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1126 : ContactPolynomial.check scale ops epsilon panel1126.row=true := by decide +kernel
theorem modelCheck1127 : panel1127.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1127 : ContactPolynomial.check scale ops epsilon panel1127.row=true := by decide +kernel
theorem modelCheck1128 : panel1128.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1128 : ContactPolynomial.check scale ops epsilon panel1128.row=true := by decide +kernel
theorem modelCheck1129 : panel1129.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1129 : ContactPolynomial.check scale ops epsilon panel1129.row=true := by decide +kernel
theorem modelCheck1130 : panel1130.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1130 : ContactPolynomial.check scale ops epsilon panel1130.row=true := by decide +kernel
theorem modelCheck1131 : panel1131.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1131 : ContactPolynomial.check scale ops epsilon panel1131.row=true := by decide +kernel
theorem modelCheck1132 : panel1132.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1132 : ContactPolynomial.check scale ops epsilon panel1132.row=true := by decide +kernel
theorem modelCheck1133 : panel1133.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1133 : ContactPolynomial.check scale ops epsilon panel1133.row=true := by decide +kernel
theorem modelCheck1134 : panel1134.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1134 : ContactPolynomial.check scale ops epsilon panel1134.row=true := by decide +kernel
theorem modelCheck1135 : panel1135.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1135 : ContactPolynomial.check scale ops epsilon panel1135.row=true := by decide +kernel
theorem modelCheck1136 : panel1136.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1136 : ContactPolynomial.check scale ops epsilon panel1136.row=true := by decide +kernel
theorem modelCheck1137 : panel1137.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1137 : ContactPolynomial.check scale ops epsilon panel1137.row=true := by decide +kernel
theorem modelCheck1138 : panel1138.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1138 : ContactPolynomial.check scale ops epsilon panel1138.row=true := by decide +kernel
theorem modelCheck1139 : panel1139.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1139 : ContactPolynomial.check scale ops epsilon panel1139.row=true := by decide +kernel
theorem modelCheck1140 : panel1140.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1140 : ContactPolynomial.check scale ops epsilon panel1140.row=true := by decide +kernel
theorem modelCheck1141 : panel1141.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1141 : ContactPolynomial.check scale ops epsilon panel1141.row=true := by decide +kernel
theorem modelCheck1142 : panel1142.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1142 : ContactPolynomial.check scale ops epsilon panel1142.row=true := by decide +kernel
theorem modelCheck1143 : panel1143.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1143 : ContactPolynomial.check scale ops epsilon panel1143.row=true := by decide +kernel
theorem modelCheck1144 : panel1144.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1144 : ContactPolynomial.check scale ops epsilon panel1144.row=true := by decide +kernel
theorem modelCheck1145 : panel1145.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1145 : ContactPolynomial.check scale ops epsilon panel1145.row=true := by decide +kernel
theorem modelCheck1146 : panel1146.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1146 : ContactPolynomial.check scale ops epsilon panel1146.row=true := by decide +kernel
theorem modelCheck1147 : panel1147.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1147 : ContactPolynomial.check scale ops epsilon panel1147.row=true := by decide +kernel
theorem modelCheck1148 : panel1148.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1148 : ContactPolynomial.check scale ops epsilon panel1148.row=true := by decide +kernel
theorem modelCheck1149 : panel1149.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1149 : ContactPolynomial.check scale ops epsilon panel1149.row=true := by decide +kernel
theorem modelCheck1150 : panel1150.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1150 : ContactPolynomial.check scale ops epsilon panel1150.row=true := by decide +kernel
theorem modelCheck1151 : panel1151.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1151 : ContactPolynomial.check scale ops epsilon panel1151.row=true := by decide +kernel
end chebyshev2.Certificates.Compact.ContactValues
