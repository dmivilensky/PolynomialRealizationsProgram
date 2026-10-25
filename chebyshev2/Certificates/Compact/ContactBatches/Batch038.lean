import chebyshev2.Certificates.Compact.ContactBatches.Data038

/-!
Article: chebyshev2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 1216–1247.
Use: `chebyshev2.Certificates.Compact.ContactValues.residualCheck1247` feeds
`chebyshev2.Certificates.Compact.ContactValues.valid1247` (valid1247).
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
theorem modelCheck1216 : panel1216.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1216 : ContactPolynomial.check scale ops epsilon panel1216.row=true := by decide +kernel
theorem modelCheck1217 : panel1217.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1217 : ContactPolynomial.check scale ops epsilon panel1217.row=true := by decide +kernel
theorem modelCheck1218 : panel1218.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1218 : ContactPolynomial.check scale ops epsilon panel1218.row=true := by decide +kernel
theorem modelCheck1219 : panel1219.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1219 : ContactPolynomial.check scale ops epsilon panel1219.row=true := by decide +kernel
theorem modelCheck1220 : panel1220.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1220 : ContactPolynomial.check scale ops epsilon panel1220.row=true := by decide +kernel
theorem modelCheck1221 : panel1221.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1221 : ContactPolynomial.check scale ops epsilon panel1221.row=true := by decide +kernel
theorem modelCheck1222 : panel1222.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1222 : ContactPolynomial.check scale ops epsilon panel1222.row=true := by decide +kernel
theorem modelCheck1223 : panel1223.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1223 : ContactPolynomial.check scale ops epsilon panel1223.row=true := by decide +kernel
theorem modelCheck1224 : panel1224.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1224 : ContactPolynomial.check scale ops epsilon panel1224.row=true := by decide +kernel
theorem modelCheck1225 : panel1225.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1225 : ContactPolynomial.check scale ops epsilon panel1225.row=true := by decide +kernel
theorem modelCheck1226 : panel1226.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1226 : ContactPolynomial.check scale ops epsilon panel1226.row=true := by decide +kernel
theorem modelCheck1227 : panel1227.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1227 : ContactPolynomial.check scale ops epsilon panel1227.row=true := by decide +kernel
theorem modelCheck1228 : panel1228.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1228 : ContactPolynomial.check scale ops epsilon panel1228.row=true := by decide +kernel
theorem modelCheck1229 : panel1229.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1229 : ContactPolynomial.check scale ops epsilon panel1229.row=true := by decide +kernel
theorem modelCheck1230 : panel1230.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1230 : ContactPolynomial.check scale ops epsilon panel1230.row=true := by decide +kernel
theorem modelCheck1231 : panel1231.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1231 : ContactPolynomial.check scale ops epsilon panel1231.row=true := by decide +kernel
theorem modelCheck1232 : panel1232.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1232 : ContactPolynomial.check scale ops epsilon panel1232.row=true := by decide +kernel
theorem modelCheck1233 : panel1233.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1233 : ContactPolynomial.check scale ops epsilon panel1233.row=true := by decide +kernel
theorem modelCheck1234 : panel1234.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1234 : ContactPolynomial.check scale ops epsilon panel1234.row=true := by decide +kernel
theorem modelCheck1235 : panel1235.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1235 : ContactPolynomial.check scale ops epsilon panel1235.row=true := by decide +kernel
theorem modelCheck1236 : panel1236.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1236 : ContactPolynomial.check scale ops epsilon panel1236.row=true := by decide +kernel
theorem modelCheck1237 : panel1237.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1237 : ContactPolynomial.check scale ops epsilon panel1237.row=true := by decide +kernel
theorem modelCheck1238 : panel1238.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1238 : ContactPolynomial.check scale ops epsilon panel1238.row=true := by decide +kernel
theorem modelCheck1239 : panel1239.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1239 : ContactPolynomial.check scale ops epsilon panel1239.row=true := by decide +kernel
theorem modelCheck1240 : panel1240.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1240 : ContactPolynomial.check scale ops epsilon panel1240.row=true := by decide +kernel
theorem modelCheck1241 : panel1241.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1241 : ContactPolynomial.check scale ops epsilon panel1241.row=true := by decide +kernel
theorem modelCheck1242 : panel1242.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1242 : ContactPolynomial.check scale ops epsilon panel1242.row=true := by decide +kernel
theorem modelCheck1243 : panel1243.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1243 : ContactPolynomial.check scale ops epsilon panel1243.row=true := by decide +kernel
theorem modelCheck1244 : panel1244.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1244 : ContactPolynomial.check scale ops epsilon panel1244.row=true := by decide +kernel
theorem modelCheck1245 : panel1245.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1245 : ContactPolynomial.check scale ops epsilon panel1245.row=true := by decide +kernel
theorem modelCheck1246 : panel1246.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1246 : ContactPolynomial.check scale ops epsilon panel1246.row=true := by decide +kernel
theorem modelCheck1247 : panel1247.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1247 : ContactPolynomial.check scale ops epsilon panel1247.row=true := by decide +kernel
end chebyshev2.Certificates.Compact.ContactValues
