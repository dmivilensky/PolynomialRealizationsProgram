import «2610.05164v2».Certificates.Compact.ContactBatches.Data037

/-!
Article: 2610.05164v2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 1184–1215.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.residualCheck1215` feeds
`«2610.05164v2».Certificates.Compact.ContactValues.valid1215` (valid1215).
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
theorem modelCheck1184 : panel1184.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1184 : ContactPolynomial.check scale ops epsilon panel1184.row=true := by decide +kernel
theorem modelCheck1185 : panel1185.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1185 : ContactPolynomial.check scale ops epsilon panel1185.row=true := by decide +kernel
theorem modelCheck1186 : panel1186.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1186 : ContactPolynomial.check scale ops epsilon panel1186.row=true := by decide +kernel
theorem modelCheck1187 : panel1187.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1187 : ContactPolynomial.check scale ops epsilon panel1187.row=true := by decide +kernel
theorem modelCheck1188 : panel1188.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1188 : ContactPolynomial.check scale ops epsilon panel1188.row=true := by decide +kernel
theorem modelCheck1189 : panel1189.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1189 : ContactPolynomial.check scale ops epsilon panel1189.row=true := by decide +kernel
theorem modelCheck1190 : panel1190.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1190 : ContactPolynomial.check scale ops epsilon panel1190.row=true := by decide +kernel
theorem modelCheck1191 : panel1191.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1191 : ContactPolynomial.check scale ops epsilon panel1191.row=true := by decide +kernel
theorem modelCheck1192 : panel1192.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1192 : ContactPolynomial.check scale ops epsilon panel1192.row=true := by decide +kernel
theorem modelCheck1193 : panel1193.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1193 : ContactPolynomial.check scale ops epsilon panel1193.row=true := by decide +kernel
theorem modelCheck1194 : panel1194.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1194 : ContactPolynomial.check scale ops epsilon panel1194.row=true := by decide +kernel
theorem modelCheck1195 : panel1195.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1195 : ContactPolynomial.check scale ops epsilon panel1195.row=true := by decide +kernel
theorem modelCheck1196 : panel1196.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1196 : ContactPolynomial.check scale ops epsilon panel1196.row=true := by decide +kernel
theorem modelCheck1197 : panel1197.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1197 : ContactPolynomial.check scale ops epsilon panel1197.row=true := by decide +kernel
theorem modelCheck1198 : panel1198.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1198 : ContactPolynomial.check scale ops epsilon panel1198.row=true := by decide +kernel
theorem modelCheck1199 : panel1199.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1199 : ContactPolynomial.check scale ops epsilon panel1199.row=true := by decide +kernel
theorem modelCheck1200 : panel1200.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1200 : ContactPolynomial.check scale ops epsilon panel1200.row=true := by decide +kernel
theorem modelCheck1201 : panel1201.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1201 : ContactPolynomial.check scale ops epsilon panel1201.row=true := by decide +kernel
theorem modelCheck1202 : panel1202.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1202 : ContactPolynomial.check scale ops epsilon panel1202.row=true := by decide +kernel
theorem modelCheck1203 : panel1203.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1203 : ContactPolynomial.check scale ops epsilon panel1203.row=true := by decide +kernel
theorem modelCheck1204 : panel1204.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1204 : ContactPolynomial.check scale ops epsilon panel1204.row=true := by decide +kernel
theorem modelCheck1205 : panel1205.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1205 : ContactPolynomial.check scale ops epsilon panel1205.row=true := by decide +kernel
theorem modelCheck1206 : panel1206.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1206 : ContactPolynomial.check scale ops epsilon panel1206.row=true := by decide +kernel
theorem modelCheck1207 : panel1207.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1207 : ContactPolynomial.check scale ops epsilon panel1207.row=true := by decide +kernel
theorem modelCheck1208 : panel1208.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1208 : ContactPolynomial.check scale ops epsilon panel1208.row=true := by decide +kernel
theorem modelCheck1209 : panel1209.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1209 : ContactPolynomial.check scale ops epsilon panel1209.row=true := by decide +kernel
theorem modelCheck1210 : panel1210.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1210 : ContactPolynomial.check scale ops epsilon panel1210.row=true := by decide +kernel
theorem modelCheck1211 : panel1211.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1211 : ContactPolynomial.check scale ops epsilon panel1211.row=true := by decide +kernel
theorem modelCheck1212 : panel1212.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1212 : ContactPolynomial.check scale ops epsilon panel1212.row=true := by decide +kernel
theorem modelCheck1213 : panel1213.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1213 : ContactPolynomial.check scale ops epsilon panel1213.row=true := by decide +kernel
theorem modelCheck1214 : panel1214.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1214 : ContactPolynomial.check scale ops epsilon panel1214.row=true := by decide +kernel
theorem modelCheck1215 : panel1215.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1215 : ContactPolynomial.check scale ops epsilon panel1215.row=true := by decide +kernel
end «2610.05164v2».Certificates.Compact.ContactValues
