import «2610.05164v2».Certificates.Compact.ContactBatches.Data026

/-!
Article: 2610.05164v2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 832–863.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.residualCheck863` feeds
`«2610.05164v2».Certificates.Compact.ContactValues.valid863` (valid863).
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
theorem modelCheck832 : panel832.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck832 : ContactPolynomial.check scale ops epsilon panel832.row=true := by decide +kernel
theorem modelCheck833 : panel833.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck833 : ContactPolynomial.check scale ops epsilon panel833.row=true := by decide +kernel
theorem modelCheck834 : panel834.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck834 : ContactPolynomial.check scale ops epsilon panel834.row=true := by decide +kernel
theorem modelCheck835 : panel835.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck835 : ContactPolynomial.check scale ops epsilon panel835.row=true := by decide +kernel
theorem modelCheck836 : panel836.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck836 : ContactPolynomial.check scale ops epsilon panel836.row=true := by decide +kernel
theorem modelCheck837 : panel837.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck837 : ContactPolynomial.check scale ops epsilon panel837.row=true := by decide +kernel
theorem modelCheck838 : panel838.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck838 : ContactPolynomial.check scale ops epsilon panel838.row=true := by decide +kernel
theorem modelCheck839 : panel839.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck839 : ContactPolynomial.check scale ops epsilon panel839.row=true := by decide +kernel
theorem modelCheck840 : panel840.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck840 : ContactPolynomial.check scale ops epsilon panel840.row=true := by decide +kernel
theorem modelCheck841 : panel841.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck841 : ContactPolynomial.check scale ops epsilon panel841.row=true := by decide +kernel
theorem modelCheck842 : panel842.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck842 : ContactPolynomial.check scale ops epsilon panel842.row=true := by decide +kernel
theorem modelCheck843 : panel843.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck843 : ContactPolynomial.check scale ops epsilon panel843.row=true := by decide +kernel
theorem modelCheck844 : panel844.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck844 : ContactPolynomial.check scale ops epsilon panel844.row=true := by decide +kernel
theorem modelCheck845 : panel845.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck845 : ContactPolynomial.check scale ops epsilon panel845.row=true := by decide +kernel
theorem modelCheck846 : panel846.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck846 : ContactPolynomial.check scale ops epsilon panel846.row=true := by decide +kernel
theorem modelCheck847 : panel847.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck847 : ContactPolynomial.check scale ops epsilon panel847.row=true := by decide +kernel
theorem modelCheck848 : panel848.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck848 : ContactPolynomial.check scale ops epsilon panel848.row=true := by decide +kernel
theorem modelCheck849 : panel849.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck849 : ContactPolynomial.check scale ops epsilon panel849.row=true := by decide +kernel
theorem modelCheck850 : panel850.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck850 : ContactPolynomial.check scale ops epsilon panel850.row=true := by decide +kernel
theorem modelCheck851 : panel851.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck851 : ContactPolynomial.check scale ops epsilon panel851.row=true := by decide +kernel
theorem modelCheck852 : panel852.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck852 : ContactPolynomial.check scale ops epsilon panel852.row=true := by decide +kernel
theorem modelCheck853 : panel853.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck853 : ContactPolynomial.check scale ops epsilon panel853.row=true := by decide +kernel
theorem modelCheck854 : panel854.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck854 : ContactPolynomial.check scale ops epsilon panel854.row=true := by decide +kernel
theorem modelCheck855 : panel855.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck855 : ContactPolynomial.check scale ops epsilon panel855.row=true := by decide +kernel
theorem modelCheck856 : panel856.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck856 : ContactPolynomial.check scale ops epsilon panel856.row=true := by decide +kernel
theorem modelCheck857 : panel857.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck857 : ContactPolynomial.check scale ops epsilon panel857.row=true := by decide +kernel
theorem modelCheck858 : panel858.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck858 : ContactPolynomial.check scale ops epsilon panel858.row=true := by decide +kernel
theorem modelCheck859 : panel859.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck859 : ContactPolynomial.check scale ops epsilon panel859.row=true := by decide +kernel
theorem modelCheck860 : panel860.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck860 : ContactPolynomial.check scale ops epsilon panel860.row=true := by decide +kernel
theorem modelCheck861 : panel861.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck861 : ContactPolynomial.check scale ops epsilon panel861.row=true := by decide +kernel
theorem modelCheck862 : panel862.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck862 : ContactPolynomial.check scale ops epsilon panel862.row=true := by decide +kernel
theorem modelCheck863 : panel863.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck863 : ContactPolynomial.check scale ops epsilon panel863.row=true := by decide +kernel
end «2610.05164v2».Certificates.Compact.ContactValues
