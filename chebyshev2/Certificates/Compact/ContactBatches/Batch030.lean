import chebyshev2.Certificates.Compact.ContactBatches.Data030

/-!
Article: chebyshev2, Section 4.1.
Kernel reduction of acceptance for contact quadrature panels 960–991.
Use: `chebyshev2.Certificates.Compact.ContactValues.residualCheck991` feeds
`chebyshev2.Certificates.Compact.ContactValues.valid991` (valid991).
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
theorem modelCheck960 : panel960.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck960 : ContactPolynomial.check scale ops epsilon panel960.row=true := by decide +kernel
theorem modelCheck961 : panel961.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck961 : ContactPolynomial.check scale ops epsilon panel961.row=true := by decide +kernel
theorem modelCheck962 : panel962.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck962 : ContactPolynomial.check scale ops epsilon panel962.row=true := by decide +kernel
theorem modelCheck963 : panel963.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck963 : ContactPolynomial.check scale ops epsilon panel963.row=true := by decide +kernel
theorem modelCheck964 : panel964.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck964 : ContactPolynomial.check scale ops epsilon panel964.row=true := by decide +kernel
theorem modelCheck965 : panel965.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck965 : ContactPolynomial.check scale ops epsilon panel965.row=true := by decide +kernel
theorem modelCheck966 : panel966.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck966 : ContactPolynomial.check scale ops epsilon panel966.row=true := by decide +kernel
theorem modelCheck967 : panel967.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck967 : ContactPolynomial.check scale ops epsilon panel967.row=true := by decide +kernel
theorem modelCheck968 : panel968.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck968 : ContactPolynomial.check scale ops epsilon panel968.row=true := by decide +kernel
theorem modelCheck969 : panel969.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck969 : ContactPolynomial.check scale ops epsilon panel969.row=true := by decide +kernel
theorem modelCheck970 : panel970.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck970 : ContactPolynomial.check scale ops epsilon panel970.row=true := by decide +kernel
theorem modelCheck971 : panel971.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck971 : ContactPolynomial.check scale ops epsilon panel971.row=true := by decide +kernel
theorem modelCheck972 : panel972.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck972 : ContactPolynomial.check scale ops epsilon panel972.row=true := by decide +kernel
theorem modelCheck973 : panel973.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck973 : ContactPolynomial.check scale ops epsilon panel973.row=true := by decide +kernel
theorem modelCheck974 : panel974.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck974 : ContactPolynomial.check scale ops epsilon panel974.row=true := by decide +kernel
theorem modelCheck975 : panel975.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck975 : ContactPolynomial.check scale ops epsilon panel975.row=true := by decide +kernel
theorem modelCheck976 : panel976.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck976 : ContactPolynomial.check scale ops epsilon panel976.row=true := by decide +kernel
theorem modelCheck977 : panel977.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck977 : ContactPolynomial.check scale ops epsilon panel977.row=true := by decide +kernel
theorem modelCheck978 : panel978.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck978 : ContactPolynomial.check scale ops epsilon panel978.row=true := by decide +kernel
theorem modelCheck979 : panel979.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck979 : ContactPolynomial.check scale ops epsilon panel979.row=true := by decide +kernel
theorem modelCheck980 : panel980.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck980 : ContactPolynomial.check scale ops epsilon panel980.row=true := by decide +kernel
theorem modelCheck981 : panel981.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck981 : ContactPolynomial.check scale ops epsilon panel981.row=true := by decide +kernel
theorem modelCheck982 : panel982.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck982 : ContactPolynomial.check scale ops epsilon panel982.row=true := by decide +kernel
theorem modelCheck983 : panel983.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck983 : ContactPolynomial.check scale ops epsilon panel983.row=true := by decide +kernel
theorem modelCheck984 : panel984.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck984 : ContactPolynomial.check scale ops epsilon panel984.row=true := by decide +kernel
theorem modelCheck985 : panel985.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck985 : ContactPolynomial.check scale ops epsilon panel985.row=true := by decide +kernel
theorem modelCheck986 : panel986.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck986 : ContactPolynomial.check scale ops epsilon panel986.row=true := by decide +kernel
theorem modelCheck987 : panel987.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck987 : ContactPolynomial.check scale ops epsilon panel987.row=true := by decide +kernel
theorem modelCheck988 : panel988.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck988 : ContactPolynomial.check scale ops epsilon panel988.row=true := by decide +kernel
theorem modelCheck989 : panel989.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck989 : ContactPolynomial.check scale ops epsilon panel989.row=true := by decide +kernel
theorem modelCheck990 : panel990.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck990 : ContactPolynomial.check scale ops epsilon panel990.row=true := by decide +kernel
theorem modelCheck991 : panel991.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck991 : ContactPolynomial.check scale ops epsilon panel991.row=true := by decide +kernel
end chebyshev2.Certificates.Compact.ContactValues
