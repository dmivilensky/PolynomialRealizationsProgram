import «2610.05164v2».Certificates.Compact.ContactBatches.Data027

/-!
Article: 2610.05164v2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 864–895.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.residualCheck895` feeds
`«2610.05164v2».Certificates.Compact.ContactValues.valid895` (valid895).
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
theorem modelCheck864 : panel864.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck864 : ContactPolynomial.check scale ops epsilon panel864.row=true := by decide +kernel
theorem modelCheck865 : panel865.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck865 : ContactPolynomial.check scale ops epsilon panel865.row=true := by decide +kernel
theorem modelCheck866 : panel866.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck866 : ContactPolynomial.check scale ops epsilon panel866.row=true := by decide +kernel
theorem modelCheck867 : panel867.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck867 : ContactPolynomial.check scale ops epsilon panel867.row=true := by decide +kernel
theorem modelCheck868 : panel868.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck868 : ContactPolynomial.check scale ops epsilon panel868.row=true := by decide +kernel
theorem modelCheck869 : panel869.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck869 : ContactPolynomial.check scale ops epsilon panel869.row=true := by decide +kernel
theorem modelCheck870 : panel870.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck870 : ContactPolynomial.check scale ops epsilon panel870.row=true := by decide +kernel
theorem modelCheck871 : panel871.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck871 : ContactPolynomial.check scale ops epsilon panel871.row=true := by decide +kernel
theorem modelCheck872 : panel872.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck872 : ContactPolynomial.check scale ops epsilon panel872.row=true := by decide +kernel
theorem modelCheck873 : panel873.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck873 : ContactPolynomial.check scale ops epsilon panel873.row=true := by decide +kernel
theorem modelCheck874 : panel874.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck874 : ContactPolynomial.check scale ops epsilon panel874.row=true := by decide +kernel
theorem modelCheck875 : panel875.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck875 : ContactPolynomial.check scale ops epsilon panel875.row=true := by decide +kernel
theorem modelCheck876 : panel876.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck876 : ContactPolynomial.check scale ops epsilon panel876.row=true := by decide +kernel
theorem modelCheck877 : panel877.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck877 : ContactPolynomial.check scale ops epsilon panel877.row=true := by decide +kernel
theorem modelCheck878 : panel878.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck878 : ContactPolynomial.check scale ops epsilon panel878.row=true := by decide +kernel
theorem modelCheck879 : panel879.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck879 : ContactPolynomial.check scale ops epsilon panel879.row=true := by decide +kernel
theorem modelCheck880 : panel880.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck880 : ContactPolynomial.check scale ops epsilon panel880.row=true := by decide +kernel
theorem modelCheck881 : panel881.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck881 : ContactPolynomial.check scale ops epsilon panel881.row=true := by decide +kernel
theorem modelCheck882 : panel882.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck882 : ContactPolynomial.check scale ops epsilon panel882.row=true := by decide +kernel
theorem modelCheck883 : panel883.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck883 : ContactPolynomial.check scale ops epsilon panel883.row=true := by decide +kernel
theorem modelCheck884 : panel884.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck884 : ContactPolynomial.check scale ops epsilon panel884.row=true := by decide +kernel
theorem modelCheck885 : panel885.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck885 : ContactPolynomial.check scale ops epsilon panel885.row=true := by decide +kernel
theorem modelCheck886 : panel886.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck886 : ContactPolynomial.check scale ops epsilon panel886.row=true := by decide +kernel
theorem modelCheck887 : panel887.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck887 : ContactPolynomial.check scale ops epsilon panel887.row=true := by decide +kernel
theorem modelCheck888 : panel888.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck888 : ContactPolynomial.check scale ops epsilon panel888.row=true := by decide +kernel
theorem modelCheck889 : panel889.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck889 : ContactPolynomial.check scale ops epsilon panel889.row=true := by decide +kernel
theorem modelCheck890 : panel890.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck890 : ContactPolynomial.check scale ops epsilon panel890.row=true := by decide +kernel
theorem modelCheck891 : panel891.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck891 : ContactPolynomial.check scale ops epsilon panel891.row=true := by decide +kernel
theorem modelCheck892 : panel892.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck892 : ContactPolynomial.check scale ops epsilon panel892.row=true := by decide +kernel
theorem modelCheck893 : panel893.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck893 : ContactPolynomial.check scale ops epsilon panel893.row=true := by decide +kernel
theorem modelCheck894 : panel894.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck894 : ContactPolynomial.check scale ops epsilon panel894.row=true := by decide +kernel
theorem modelCheck895 : panel895.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck895 : ContactPolynomial.check scale ops epsilon panel895.row=true := by decide +kernel
end «2610.05164v2».Certificates.Compact.ContactValues
