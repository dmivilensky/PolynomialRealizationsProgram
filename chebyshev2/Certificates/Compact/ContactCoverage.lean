import chebyshev2.Certificates.Compact.ContactShared
import chebyshev2.Certificates.Compact.ReferenceTrajectoryData

/-!
Article: chebyshev2, Section 4.1.
Contact Coverage.
Use: `chebyshev2.Certificates.Compact.ContactValues.ValidPanel` feeds
`chebyshev2.Certificates.Compact.AmplitudeValues.valid1216` (valid1216).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace chebyshev2.Certificates.Compact.ContactValues
open chebyshev2.Numerics.IntegerCertificate
set_option autoImplicit false

/--
Defines `ValidPanel` of type `Prop` by `p.modelCheck scale piBounds leftRadius rightRadius=true
∧ ContactPolynomial.check scale ops epsilon p.row=true ∧ p.left∈ReferenceTrajectory.leftRows ∧
p.right∈ReferenceTrajectory.rightRows`.

Use: `chebyshev2.Certificates.Compact.AmplitudeValues.ValidPanel` uses this definition in
the displayed construction of `ValidPanel`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def ValidPanel (p : ContactPolynomial.Panel) : Prop :=
  p.modelCheck scale piBounds leftRadius rightRadius=true ∧
  ContactPolynomial.check scale ops epsilon p.row=true ∧
  p.left∈ReferenceTrajectory.leftRows ∧ p.right∈ReferenceTrajectory.rightRows

end chebyshev2.Certificates.Compact.ContactValues
