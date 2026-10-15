import «2610.05164v2».Certificates.Compact.ContactBatches.Data039

/-!
Article: 2610.05164v2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 1248–1279.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.residualCheck1279` feeds
`«2610.05164v2».Certificates.Compact.ContactValues.valid1279` (valid1279).
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
theorem modelCheck1248 : panel1248.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1248 : ContactPolynomial.check scale ops epsilon panel1248.row=true := by decide +kernel
theorem modelCheck1249 : panel1249.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1249 : ContactPolynomial.check scale ops epsilon panel1249.row=true := by decide +kernel
theorem modelCheck1250 : panel1250.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1250 : ContactPolynomial.check scale ops epsilon panel1250.row=true := by decide +kernel
theorem modelCheck1251 : panel1251.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1251 : ContactPolynomial.check scale ops epsilon panel1251.row=true := by decide +kernel
theorem modelCheck1252 : panel1252.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1252 : ContactPolynomial.check scale ops epsilon panel1252.row=true := by decide +kernel
theorem modelCheck1253 : panel1253.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1253 : ContactPolynomial.check scale ops epsilon panel1253.row=true := by decide +kernel
theorem modelCheck1254 : panel1254.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1254 : ContactPolynomial.check scale ops epsilon panel1254.row=true := by decide +kernel
theorem modelCheck1255 : panel1255.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1255 : ContactPolynomial.check scale ops epsilon panel1255.row=true := by decide +kernel
theorem modelCheck1256 : panel1256.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1256 : ContactPolynomial.check scale ops epsilon panel1256.row=true := by decide +kernel
theorem modelCheck1257 : panel1257.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1257 : ContactPolynomial.check scale ops epsilon panel1257.row=true := by decide +kernel
theorem modelCheck1258 : panel1258.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1258 : ContactPolynomial.check scale ops epsilon panel1258.row=true := by decide +kernel
theorem modelCheck1259 : panel1259.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1259 : ContactPolynomial.check scale ops epsilon panel1259.row=true := by decide +kernel
theorem modelCheck1260 : panel1260.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1260 : ContactPolynomial.check scale ops epsilon panel1260.row=true := by decide +kernel
theorem modelCheck1261 : panel1261.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1261 : ContactPolynomial.check scale ops epsilon panel1261.row=true := by decide +kernel
theorem modelCheck1262 : panel1262.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1262 : ContactPolynomial.check scale ops epsilon panel1262.row=true := by decide +kernel
theorem modelCheck1263 : panel1263.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1263 : ContactPolynomial.check scale ops epsilon panel1263.row=true := by decide +kernel
theorem modelCheck1264 : panel1264.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1264 : ContactPolynomial.check scale ops epsilon panel1264.row=true := by decide +kernel
theorem modelCheck1265 : panel1265.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1265 : ContactPolynomial.check scale ops epsilon panel1265.row=true := by decide +kernel
theorem modelCheck1266 : panel1266.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1266 : ContactPolynomial.check scale ops epsilon panel1266.row=true := by decide +kernel
theorem modelCheck1267 : panel1267.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1267 : ContactPolynomial.check scale ops epsilon panel1267.row=true := by decide +kernel
theorem modelCheck1268 : panel1268.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1268 : ContactPolynomial.check scale ops epsilon panel1268.row=true := by decide +kernel
theorem modelCheck1269 : panel1269.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1269 : ContactPolynomial.check scale ops epsilon panel1269.row=true := by decide +kernel
theorem modelCheck1270 : panel1270.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1270 : ContactPolynomial.check scale ops epsilon panel1270.row=true := by decide +kernel
theorem modelCheck1271 : panel1271.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1271 : ContactPolynomial.check scale ops epsilon panel1271.row=true := by decide +kernel
theorem modelCheck1272 : panel1272.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1272 : ContactPolynomial.check scale ops epsilon panel1272.row=true := by decide +kernel
theorem modelCheck1273 : panel1273.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1273 : ContactPolynomial.check scale ops epsilon panel1273.row=true := by decide +kernel
theorem modelCheck1274 : panel1274.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1274 : ContactPolynomial.check scale ops epsilon panel1274.row=true := by decide +kernel
theorem modelCheck1275 : panel1275.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1275 : ContactPolynomial.check scale ops epsilon panel1275.row=true := by decide +kernel
theorem modelCheck1276 : panel1276.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1276 : ContactPolynomial.check scale ops epsilon panel1276.row=true := by decide +kernel
theorem modelCheck1277 : panel1277.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1277 : ContactPolynomial.check scale ops epsilon panel1277.row=true := by decide +kernel
theorem modelCheck1278 : panel1278.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1278 : ContactPolynomial.check scale ops epsilon panel1278.row=true := by decide +kernel
theorem modelCheck1279 : panel1279.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1279 : ContactPolynomial.check scale ops epsilon panel1279.row=true := by decide +kernel
end «2610.05164v2».Certificates.Compact.ContactValues
