import «2610.05164v2».Certificates.Compact.ContactShared
import «2610.05164v2».Certificates.Compact.ReferenceTrajectoryData

/-!
Article: 2610.05164v2, Section 4.1.
Contact Coverage.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.ValidPanel` feeds
`«2610.05164v2».Certificates.Compact.AmplitudeValues.valid1216` (valid1216).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace «2610.05164v2».Certificates.Compact.ContactValues
open «2610.05164v2».Numerics.IntegerCertificate
set_option autoImplicit false

/--
Defines `ValidPanel` of type `Prop` by `p.modelCheck scale piBounds leftRadius rightRadius=true
∧ ContactPolynomial.check scale ops epsilon p.row=true ∧ p.left∈ReferenceTrajectory.leftRows ∧
p.right∈ReferenceTrajectory.rightRows`.

Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.ValidPanel` uses this definition in
the displayed construction of `ValidPanel`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def ValidPanel (p : ContactPolynomial.Panel) : Prop :=
  p.modelCheck scale piBounds leftRadius rightRadius=true ∧
  ContactPolynomial.check scale ops epsilon p.row=true ∧
  p.left∈ReferenceTrajectory.leftRows ∧ p.right∈ReferenceTrajectory.rightRows

end «2610.05164v2».Certificates.Compact.ContactValues
