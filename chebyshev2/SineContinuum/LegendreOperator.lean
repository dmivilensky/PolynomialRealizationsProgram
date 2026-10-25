import chebyshev2.SineContinuum.LegendreHilbertBasis
import chebyshev2.Continuum.UnboundedDiagonal

/-!
Article: chebyshev2, Lemma 5.
Self-adjointness uses mathlib's genuine adjoint of an unbounded operator.
Use: `chebyshev2.SineContinuum.legendreOperator` feeds
`chebyshev2.SineContinuum.affineLegendre_domain` (affine Legendre domain).
Proof chain: `chebyshev2.SineContinuum.legendreV_domain` — chebyshev2, Lemma 5; Legendre
operator, nonlogarithmic realization and continuum sine spectrum.
Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation. The needed form is proved here.
-/
namespace chebyshev2.SineContinuum
noncomputable section
open MeasureTheory
attribute [local instance] Measure.Subtype.measureSpace

/--
The nonnegative Legendre operator, initially in the equivalent shifted unit-interval
coordinates. Its domain is the full weighted ℓ² domain.

Use: `chebyshev2.SineContinuum.legendreOperator_basis` uses this definition to establish
the precise assertion is `legendreOperator ⟨legendreHilbertBasis n,legendreOperator_basis_mem
n⟩= ((n:ℝ)*(n+1)) • legendreHilbertBasis n`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
def legendreOperator : LegendreSpace →ₗ.[ℝ] LegendreSpace :=
  Continuum.unboundedDiagonalOperator legendreHilbertBasis (fun n => (n:ℝ)*(n+1))

/--
Equivalence of the displayed criteria: `u ∈ legendreOperator.domain ↔ Summable (fun n : ℕ =>
(n:ℝ)^2*((n:ℝ)+1)^2*(legendreHilbertBasis.repr u n)^2)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 5.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: Use the identities/estimates `chebyshev2.Continuum.unboundedDiagonalDomain_iff` with
the arguments shown in the proof.
-/
theorem legendreOperator_domain (u : LegendreSpace) :
    u ∈ legendreOperator.domain ↔
      Summable (fun n : ℕ => (n:ℝ)^2*((n:ℝ)+1)^2*(legendreHilbertBasis.repr u n)^2) := by
  change u ∈ Continuum.unboundedDiagonalDomain legendreHilbertBasis (fun n => (n:ℝ)*(n+1)) ↔ _
  simpa only [mul_pow,mul_assoc] using
    Continuum.unboundedDiagonalDomain_iff legendreHilbertBasis (fun n => (n:ℝ)*(n+1)) u

/--
Membership in the specified domain/enclosure: `legendreHilbertBasis n ∈
legendreOperator.domain`.

Use: `chebyshev2.SineContinuum.legendreOperator_basis` uses this assertion to establish the
precise assertion is `legendreOperator ⟨legendreHilbertBasis n,legendreOperator_basis_mem n⟩=
((n:ℝ)*(n+1)) • legendreHilbertBasis n`.

Article: chebyshev2, Lemma 5.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: Use the identities/estimates `chebyshev2.Continuum.unboundedDiagonalDomain_basis`
with the arguments shown in the proof.
-/
theorem legendreOperator_basis_mem (n : ℕ) : legendreHilbertBasis n ∈ legendreOperator.domain :=
  Continuum.unboundedDiagonalDomain_basis _ _ n

/--
The precise assertion is `legendreOperator ⟨legendreHilbertBasis n,legendreOperator_basis_mem
n⟩= ((n:ℝ)*(n+1)) • legendreHilbertBasis n`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 5.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: Use the identities/estimates `chebyshev2.Continuum.unboundedDiagonalOperator_basis`
with the arguments shown in the proof.
-/
theorem legendreOperator_basis (n : ℕ) :
    legendreOperator ⟨legendreHilbertBasis n,legendreOperator_basis_mem n⟩=
      ((n:ℝ)*(n+1)) • legendreHilbertBasis n :=
  Continuum.unboundedDiagonalOperator_basis _ _ n

/--
Self-adjointness uses mathlib's genuine adjoint of an unbounded operator.

Exact identity `legendreOperator.adjoint=legendreOperator`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 5.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: Use the identities/estimates
`chebyshev2.Continuum.unboundedDiagonalOperator_selfAdjoint` with the arguments shown in
the proof.
-/
theorem legendreOperator_selfAdjoint : legendreOperator.adjoint=legendreOperator :=
  Continuum.unboundedDiagonalOperator_selfAdjoint _ _

/--
The precise assertion is `Dense (legendreOperator.domain : Set LegendreSpace)`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 5.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: Use the identities/estimates `chebyshev2.Continuum.unboundedDiagonalDomain_dense`
with the arguments shown in the proof.
-/
theorem legendreOperator_dense : Dense (legendreOperator.domain : Set LegendreSpace) :=
  Continuum.unboundedDiagonalDomain_dense _ _

/--
The stated quantitative bound `0 ≤ inner ℝ (legendreOperator u) (u:LegendreSpace)`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 5.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: Use the identities/estimates
`chebyshev2.Continuum.unboundedDiagonalOperator_nonnegative` with the arguments shown in
the proof.
-/
theorem legendreOperator_nonnegative (u : legendreOperator.domain) :
    0 ≤ inner ℝ (legendreOperator u) (u:LegendreSpace) :=
  Continuum.unboundedDiagonalOperator_nonnegative _ _ (fun n => by positivity) u

end
end chebyshev2.SineContinuum
