import chebyshev2.SineContinuum.LegendrePolynomials
import Mathlib.Algebra.Polynomial.Sequence

/-!
Article: chebyshev2, Lemma 5.
Every real polynomial is a finite linear combination of shifted Legendre polynomials.
Use: `chebyshev2.SineContinuum.shifted_span` feeds
`chebyshev2.SineContinuum.normalizedLegendre_span_dense` (normalized Legendre span dense).
Proof chain: `chebyshev2.SineContinuum.legendreV_domain` — chebyshev2, Lemma 5; Legendre
operator, nonlogarithmic realization and continuum sine spectrum.
Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation. The needed form is proved here.
-/
namespace chebyshev2.SineContinuum
noncomputable section
open Polynomial

/--
The exact community Legendre polynomials have degree equal to their index.

Exact identity `(shifted n).degree=n`.

Use: `chebyshev2.SineContinuum.legendreSequence` uses this identity in the displayed
construction of `legendreSequence`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem shifted_degree (n : ℕ) : (shifted n).degree=n := by rw [shifted, degree_map_eq_of_injective (Int.cast_injective), degree_shiftedLegendre]

/--
Constructs `legendreSequence` of type `Polynomial.Sequence ℝ` by the displayed record fields.
Data fields specify the construction; proof fields discharge its required properties.

Use: `chebyshev2.SineContinuum.legendrePolynomialBasis` uses this definition in the
displayed construction of `legendrePolynomialBasis`. Its inputs and component formulas are
fixed by that definition.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
def legendreSequence : Polynomial.Sequence ℝ where
  elems' := shifted
  degree_eq' := shifted_degree

/--
Every real polynomial is a finite linear combination of shifted Legendre polynomials. This
reuses mathlib's general polynomial-sequence basis.

Use: `chebyshev2.SineContinuum.shifted_span` uses this definition to establish exact
identity `Submodule.span ℝ (Set.range shifted)=⊤`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
def legendrePolynomialBasis : Module.Basis ℕ ℝ (Polynomial ℝ) :=
  legendreSequence.basis (fun n => isUnit_iff_ne_zero.mpr
    (leadingCoeff_ne_zero.mpr (legendreSequence.ne_zero n)))

/--
Exact identity `legendrePolynomialBasis n=shifted n`.

Use: `chebyshev2.SineContinuum.shifted_span` uses this identity to establish the identity
`Submodule.span ℝ (Set.range shifted)=⊤`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem legendrePolynomialBasis_apply (n : ℕ) : legendrePolynomialBasis n=shifted n :=
  legendreSequence.basis_eq_self _ n

/--
Exact identity `Submodule.span ℝ (Set.range shifted)=⊤`.

Use: `chebyshev2.SineContinuum.normalizedLegendre_span_dense` rewrites with this identity
to establish the identity `(Submodule.span ℝ (range
normalizedLegendre)).topologicalClosure=⊤`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem shifted_span : Submodule.span ℝ (Set.range shifted)=⊤ := by
  have hf : (fun n => legendrePolynomialBasis n)=shifted := funext legendrePolynomialBasis_apply
  rw [← hf]
  exact legendrePolynomialBasis.span_eq

end
end chebyshev2.SineContinuum
