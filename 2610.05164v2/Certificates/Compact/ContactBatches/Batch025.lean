import «2610.05164v2».Certificates.Compact.ContactBatches.Data025

/-!
Article: 2610.05164v2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 800–831.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.residualCheck831` feeds
`«2610.05164v2».Certificates.Compact.ContactValues.valid831` (valid831).
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
theorem modelCheck800 : panel800.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck800 : ContactPolynomial.check scale ops epsilon panel800.row=true := by decide +kernel
theorem modelCheck801 : panel801.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck801 : ContactPolynomial.check scale ops epsilon panel801.row=true := by decide +kernel
theorem modelCheck802 : panel802.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck802 : ContactPolynomial.check scale ops epsilon panel802.row=true := by decide +kernel
theorem modelCheck803 : panel803.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck803 : ContactPolynomial.check scale ops epsilon panel803.row=true := by decide +kernel
theorem modelCheck804 : panel804.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck804 : ContactPolynomial.check scale ops epsilon panel804.row=true := by decide +kernel
theorem modelCheck805 : panel805.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck805 : ContactPolynomial.check scale ops epsilon panel805.row=true := by decide +kernel
theorem modelCheck806 : panel806.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck806 : ContactPolynomial.check scale ops epsilon panel806.row=true := by decide +kernel
theorem modelCheck807 : panel807.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck807 : ContactPolynomial.check scale ops epsilon panel807.row=true := by decide +kernel
theorem modelCheck808 : panel808.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck808 : ContactPolynomial.check scale ops epsilon panel808.row=true := by decide +kernel
theorem modelCheck809 : panel809.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck809 : ContactPolynomial.check scale ops epsilon panel809.row=true := by decide +kernel
theorem modelCheck810 : panel810.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck810 : ContactPolynomial.check scale ops epsilon panel810.row=true := by decide +kernel
theorem modelCheck811 : panel811.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck811 : ContactPolynomial.check scale ops epsilon panel811.row=true := by decide +kernel
theorem modelCheck812 : panel812.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck812 : ContactPolynomial.check scale ops epsilon panel812.row=true := by decide +kernel
theorem modelCheck813 : panel813.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck813 : ContactPolynomial.check scale ops epsilon panel813.row=true := by decide +kernel
theorem modelCheck814 : panel814.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck814 : ContactPolynomial.check scale ops epsilon panel814.row=true := by decide +kernel
theorem modelCheck815 : panel815.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck815 : ContactPolynomial.check scale ops epsilon panel815.row=true := by decide +kernel
theorem modelCheck816 : panel816.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck816 : ContactPolynomial.check scale ops epsilon panel816.row=true := by decide +kernel
theorem modelCheck817 : panel817.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck817 : ContactPolynomial.check scale ops epsilon panel817.row=true := by decide +kernel
theorem modelCheck818 : panel818.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck818 : ContactPolynomial.check scale ops epsilon panel818.row=true := by decide +kernel
theorem modelCheck819 : panel819.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck819 : ContactPolynomial.check scale ops epsilon panel819.row=true := by decide +kernel
theorem modelCheck820 : panel820.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck820 : ContactPolynomial.check scale ops epsilon panel820.row=true := by decide +kernel
theorem modelCheck821 : panel821.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck821 : ContactPolynomial.check scale ops epsilon panel821.row=true := by decide +kernel
theorem modelCheck822 : panel822.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck822 : ContactPolynomial.check scale ops epsilon panel822.row=true := by decide +kernel
theorem modelCheck823 : panel823.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck823 : ContactPolynomial.check scale ops epsilon panel823.row=true := by decide +kernel
theorem modelCheck824 : panel824.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck824 : ContactPolynomial.check scale ops epsilon panel824.row=true := by decide +kernel
theorem modelCheck825 : panel825.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck825 : ContactPolynomial.check scale ops epsilon panel825.row=true := by decide +kernel
theorem modelCheck826 : panel826.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck826 : ContactPolynomial.check scale ops epsilon panel826.row=true := by decide +kernel
theorem modelCheck827 : panel827.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck827 : ContactPolynomial.check scale ops epsilon panel827.row=true := by decide +kernel
theorem modelCheck828 : panel828.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck828 : ContactPolynomial.check scale ops epsilon panel828.row=true := by decide +kernel
theorem modelCheck829 : panel829.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck829 : ContactPolynomial.check scale ops epsilon panel829.row=true := by decide +kernel
theorem modelCheck830 : panel830.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck830 : ContactPolynomial.check scale ops epsilon panel830.row=true := by decide +kernel
theorem modelCheck831 : panel831.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck831 : ContactPolynomial.check scale ops epsilon panel831.row=true := by decide +kernel
end «2610.05164v2».Certificates.Compact.ContactValues
