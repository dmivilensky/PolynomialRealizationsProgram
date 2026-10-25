import chebyshev2.Numerics.IntegerTaylorModel

/-!
Article: chebyshev2, Section 4.1.
Taylor Input Extension.
Use: `chebyshev2.Numerics.IntegerCertificate.Poly.Taylor.cons_encloses` feeds
`chebyshev2.Numerics.IntegerCertificate.AmplitudePolynomial.Panel.actual_of_inputs` (actual of
inputs).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace chebyshev2.Numerics.IntegerCertificate.Poly.Taylor
set_option autoImplicit false

/--
Defines `pushValue` by pattern matching with result type `Nat → ℝ`. The displayed branches
determine the recursive cases and their returned values.

Use: `chebyshev2.Numerics.IntegerCertificate.Poly.Taylor.cons_encloses` uses this
definition to establish `Encloses s (I::stack) x (pushValue a v)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
noncomputable def pushValue (a : ℝ) (v : Nat → ℝ) : Nat → ℝ
  | 0 => a
  | i+1 => v i

/--
The precise assertion is `Encloses s (I::stack) x (pushValue a v)`.

Use: `chebyshev2.Numerics.IntegerCertificate.AmplitudePolynomial.Panel.actual_of_inputs`
uses this assertion to establish the identity stated in that declaration.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem cons_encloses {s : Nat} {stack : List (List Bounds)} {I : List Bounds}
    {x a : ℝ} {v : Nat → ℝ} (ha : At s I x a) (hv : Encloses s stack x v) :
    Encloses s (I::stack) x (pushValue a v) := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  intro i J hi
  cases i with
  | zero =>
    have he : I=J := by simpa using hi
    simpa only [← he,pushValue] using ha
  | succ i => exact hv i J (by simpa using hi)

end chebyshev2.Numerics.IntegerCertificate.Poly.Taylor
