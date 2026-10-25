import chebyshev2.Certificates.Compact.ContactBatches.Data036

/-!
Article: chebyshev2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 1152–1183.
Use: `chebyshev2.Certificates.Compact.ContactValues.residualCheck1183` feeds
`chebyshev2.Certificates.Compact.ContactValues.valid1183` (valid1183).
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
theorem modelCheck1152 : panel1152.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1152 : ContactPolynomial.check scale ops epsilon panel1152.row=true := by decide +kernel
theorem modelCheck1153 : panel1153.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1153 : ContactPolynomial.check scale ops epsilon panel1153.row=true := by decide +kernel
theorem modelCheck1154 : panel1154.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1154 : ContactPolynomial.check scale ops epsilon panel1154.row=true := by decide +kernel
theorem modelCheck1155 : panel1155.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1155 : ContactPolynomial.check scale ops epsilon panel1155.row=true := by decide +kernel
theorem modelCheck1156 : panel1156.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1156 : ContactPolynomial.check scale ops epsilon panel1156.row=true := by decide +kernel
theorem modelCheck1157 : panel1157.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1157 : ContactPolynomial.check scale ops epsilon panel1157.row=true := by decide +kernel
theorem modelCheck1158 : panel1158.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1158 : ContactPolynomial.check scale ops epsilon panel1158.row=true := by decide +kernel
theorem modelCheck1159 : panel1159.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1159 : ContactPolynomial.check scale ops epsilon panel1159.row=true := by decide +kernel
theorem modelCheck1160 : panel1160.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1160 : ContactPolynomial.check scale ops epsilon panel1160.row=true := by decide +kernel
theorem modelCheck1161 : panel1161.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1161 : ContactPolynomial.check scale ops epsilon panel1161.row=true := by decide +kernel
theorem modelCheck1162 : panel1162.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1162 : ContactPolynomial.check scale ops epsilon panel1162.row=true := by decide +kernel
theorem modelCheck1163 : panel1163.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1163 : ContactPolynomial.check scale ops epsilon panel1163.row=true := by decide +kernel
theorem modelCheck1164 : panel1164.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1164 : ContactPolynomial.check scale ops epsilon panel1164.row=true := by decide +kernel
theorem modelCheck1165 : panel1165.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1165 : ContactPolynomial.check scale ops epsilon panel1165.row=true := by decide +kernel
theorem modelCheck1166 : panel1166.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1166 : ContactPolynomial.check scale ops epsilon panel1166.row=true := by decide +kernel
theorem modelCheck1167 : panel1167.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1167 : ContactPolynomial.check scale ops epsilon panel1167.row=true := by decide +kernel
theorem modelCheck1168 : panel1168.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1168 : ContactPolynomial.check scale ops epsilon panel1168.row=true := by decide +kernel
theorem modelCheck1169 : panel1169.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1169 : ContactPolynomial.check scale ops epsilon panel1169.row=true := by decide +kernel
theorem modelCheck1170 : panel1170.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1170 : ContactPolynomial.check scale ops epsilon panel1170.row=true := by decide +kernel
theorem modelCheck1171 : panel1171.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1171 : ContactPolynomial.check scale ops epsilon panel1171.row=true := by decide +kernel
theorem modelCheck1172 : panel1172.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1172 : ContactPolynomial.check scale ops epsilon panel1172.row=true := by decide +kernel
theorem modelCheck1173 : panel1173.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1173 : ContactPolynomial.check scale ops epsilon panel1173.row=true := by decide +kernel
theorem modelCheck1174 : panel1174.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1174 : ContactPolynomial.check scale ops epsilon panel1174.row=true := by decide +kernel
theorem modelCheck1175 : panel1175.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1175 : ContactPolynomial.check scale ops epsilon panel1175.row=true := by decide +kernel
theorem modelCheck1176 : panel1176.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1176 : ContactPolynomial.check scale ops epsilon panel1176.row=true := by decide +kernel
theorem modelCheck1177 : panel1177.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1177 : ContactPolynomial.check scale ops epsilon panel1177.row=true := by decide +kernel
theorem modelCheck1178 : panel1178.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1178 : ContactPolynomial.check scale ops epsilon panel1178.row=true := by decide +kernel
theorem modelCheck1179 : panel1179.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1179 : ContactPolynomial.check scale ops epsilon panel1179.row=true := by decide +kernel
theorem modelCheck1180 : panel1180.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1180 : ContactPolynomial.check scale ops epsilon panel1180.row=true := by decide +kernel
theorem modelCheck1181 : panel1181.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1181 : ContactPolynomial.check scale ops epsilon panel1181.row=true := by decide +kernel
theorem modelCheck1182 : panel1182.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1182 : ContactPolynomial.check scale ops epsilon panel1182.row=true := by decide +kernel
theorem modelCheck1183 : panel1183.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1183 : ContactPolynomial.check scale ops epsilon panel1183.row=true := by decide +kernel
end chebyshev2.Certificates.Compact.ContactValues
