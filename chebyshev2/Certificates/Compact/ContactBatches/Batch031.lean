import chebyshev2.Certificates.Compact.ContactBatches.Data031

/-!
Article: chebyshev2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 992–1023.
Use: `chebyshev2.Certificates.Compact.ContactValues.residualCheck1023` feeds
`chebyshev2.Certificates.Compact.ContactValues.valid1023` (valid1023).
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
theorem modelCheck992 : panel992.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck992 : ContactPolynomial.check scale ops epsilon panel992.row=true := by decide +kernel
theorem modelCheck993 : panel993.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck993 : ContactPolynomial.check scale ops epsilon panel993.row=true := by decide +kernel
theorem modelCheck994 : panel994.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck994 : ContactPolynomial.check scale ops epsilon panel994.row=true := by decide +kernel
theorem modelCheck995 : panel995.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck995 : ContactPolynomial.check scale ops epsilon panel995.row=true := by decide +kernel
theorem modelCheck996 : panel996.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck996 : ContactPolynomial.check scale ops epsilon panel996.row=true := by decide +kernel
theorem modelCheck997 : panel997.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck997 : ContactPolynomial.check scale ops epsilon panel997.row=true := by decide +kernel
theorem modelCheck998 : panel998.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck998 : ContactPolynomial.check scale ops epsilon panel998.row=true := by decide +kernel
theorem modelCheck999 : panel999.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck999 : ContactPolynomial.check scale ops epsilon panel999.row=true := by decide +kernel
theorem modelCheck1000 : panel1000.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1000 : ContactPolynomial.check scale ops epsilon panel1000.row=true := by decide +kernel
theorem modelCheck1001 : panel1001.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1001 : ContactPolynomial.check scale ops epsilon panel1001.row=true := by decide +kernel
theorem modelCheck1002 : panel1002.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1002 : ContactPolynomial.check scale ops epsilon panel1002.row=true := by decide +kernel
theorem modelCheck1003 : panel1003.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1003 : ContactPolynomial.check scale ops epsilon panel1003.row=true := by decide +kernel
theorem modelCheck1004 : panel1004.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1004 : ContactPolynomial.check scale ops epsilon panel1004.row=true := by decide +kernel
theorem modelCheck1005 : panel1005.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1005 : ContactPolynomial.check scale ops epsilon panel1005.row=true := by decide +kernel
theorem modelCheck1006 : panel1006.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1006 : ContactPolynomial.check scale ops epsilon panel1006.row=true := by decide +kernel
theorem modelCheck1007 : panel1007.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1007 : ContactPolynomial.check scale ops epsilon panel1007.row=true := by decide +kernel
theorem modelCheck1008 : panel1008.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1008 : ContactPolynomial.check scale ops epsilon panel1008.row=true := by decide +kernel
theorem modelCheck1009 : panel1009.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1009 : ContactPolynomial.check scale ops epsilon panel1009.row=true := by decide +kernel
theorem modelCheck1010 : panel1010.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1010 : ContactPolynomial.check scale ops epsilon panel1010.row=true := by decide +kernel
theorem modelCheck1011 : panel1011.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1011 : ContactPolynomial.check scale ops epsilon panel1011.row=true := by decide +kernel
theorem modelCheck1012 : panel1012.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1012 : ContactPolynomial.check scale ops epsilon panel1012.row=true := by decide +kernel
theorem modelCheck1013 : panel1013.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1013 : ContactPolynomial.check scale ops epsilon panel1013.row=true := by decide +kernel
theorem modelCheck1014 : panel1014.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1014 : ContactPolynomial.check scale ops epsilon panel1014.row=true := by decide +kernel
theorem modelCheck1015 : panel1015.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1015 : ContactPolynomial.check scale ops epsilon panel1015.row=true := by decide +kernel
theorem modelCheck1016 : panel1016.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1016 : ContactPolynomial.check scale ops epsilon panel1016.row=true := by decide +kernel
theorem modelCheck1017 : panel1017.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1017 : ContactPolynomial.check scale ops epsilon panel1017.row=true := by decide +kernel
theorem modelCheck1018 : panel1018.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1018 : ContactPolynomial.check scale ops epsilon panel1018.row=true := by decide +kernel
theorem modelCheck1019 : panel1019.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1019 : ContactPolynomial.check scale ops epsilon panel1019.row=true := by decide +kernel
theorem modelCheck1020 : panel1020.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1020 : ContactPolynomial.check scale ops epsilon panel1020.row=true := by decide +kernel
theorem modelCheck1021 : panel1021.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1021 : ContactPolynomial.check scale ops epsilon panel1021.row=true := by decide +kernel
theorem modelCheck1022 : panel1022.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1022 : ContactPolynomial.check scale ops epsilon panel1022.row=true := by decide +kernel
theorem modelCheck1023 : panel1023.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck1023 : ContactPolynomial.check scale ops epsilon panel1023.row=true := by decide +kernel
end chebyshev2.Certificates.Compact.ContactValues
