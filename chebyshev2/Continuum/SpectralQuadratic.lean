import chebyshev2.Continuum.PositiveSpectrum

/-!
Article: chebyshev2, Theorem 2.3.
Membership in the selected subspace gives the corresponding Rayleigh lower bound, with no assumed
min--max theorem.
Use: `chebyshev2.Continuum.PositiveSpectralData.quadratic_ge_of_selected` feeds
`chebyshev2.Continuum.eigenvalue_mono` (Eigenvalue monotonicity, proved by the dimension
argument behind min--max).
Proof chain: `chebyshev2.Packing.packed_spectral_distance` — chebyshev2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory. The needed
form is proved here.
-/
namespace chebyshev2.Continuum
noncomputable section
open MeasureTheory Real
open scoped InnerProductSpace BigOperators Classical
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/--
The value of a convergent infinite sum: `HasSum (fun i => eig i * inner ℝ (b i) x^2) (inner ℝ x
(T x))`.

Use: `chebyshev2.Continuum.PositiveSpectralData.quadratic_ge_of_selected` uses this
infinite-sum formula to prove the bound `D.eigenvalue n * ‖x‖^2 ≤ inner
ℝ x (T x)`.

Article: chebyshev2, Theorem 2.4 via
`chebyshev2.Continuum.kernelEigenvalue_square_integral`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem eigenbasis_quadratic_hasSum {ι : Type*} (b : HilbertBasis ι ℝ E)
    (T : E →L[ℝ] E) {eig : ι → ℝ} (he : ∀ i, T (b i) = eig i • b i) (x : E) :
    HasSum (fun i => eig i * inner ℝ (b i) x^2) (inner ℝ x (T x)) := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  have h := ((innerSL ℝ x).comp T).hasSum (b.hasSum_repr x)
  have hi (i : ι) : ((innerSL ℝ x).comp T) (b.repr x i • b i) = eig i * inner ℝ (b i) x^2 := by
    change inner ℝ x (T (b.repr x i • b i)) = _
    rw [map_smul,he,real_inner_smul_right,real_inner_smul_right,HilbertBasis.repr_apply_apply,
      real_inner_comm x (b i)]
    ring
  simp only [hi] at h
  exact h

namespace PositiveSpectralData
variable {T : E →L[ℝ] E} (D : PositiveSpectralData T)

/--
Rayleigh upper bound on the orthogonal complement of the first n selected basis vectors. The
selected set automatically handles zero padding.

The stated quantitative bound `inner ℝ x (T x) ≤ D.eigenvalue n * ‖x‖^2`.

Use: `chebyshev2.Continuum.PositiveSpectralData.top_quadratic_bound` uses this bound to
establish the stated quantitative bound `inner ℝ x (T x) ≤ D.eigenvalue 0*‖x‖^2`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Separate `i ∈ spectralSelected D.summable n` from its negation; prove the goal under
each of these mutually exclusive hypotheses.
-/
theorem quadratic_le_eigenvalue (n : ℕ) (x : E)
    (hx : ∀ i ∈ spectralSelected D.summable n, inner ℝ (D.basis i) x = 0) :
    inner ℝ x (T x) ≤ D.eigenvalue n * ‖x‖^2 := by
  -- Separate `i ∈ spectralSelected D.summable n` from its negation; prove the goal under each
  -- of these mutually exclusive hypotheses.
  have h₁ := eigenbasis_quadratic_hasSum D.basis T D.equation x
  have h₂ := (basis_hasSum_sq D.basis x).mul_left (D.eigenvalue n)
  apply hasSum_le _ h₁ h₂
  intro i
  by_cases hi : i ∈ spectralSelected D.summable n
  · simp only [hx i hi,zero_pow (by norm_num : (2:ℕ) ≠ 0),mul_zero,le_refl]
  · exact mul_le_mul_of_nonneg_right (spectralSorted_max D.summable n hi) (sq_nonneg _)

/--
Membership in the selected subspace gives the corresponding Rayleigh lower bound, with no
assumed min--max theorem.

The stated quantitative bound `D.eigenvalue n * ‖x‖^2 ≤ inner ℝ x (T x)`.

Use: `chebyshev2.Continuum.eigenvalue_mono` uses this bound to establish the stated
quantitative bound `DA.eigenvalue n ≤ DB.eigenvalue n`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Separate `i ∈ spectralSelected D.summable (n+1)` from its negation; prove the goal under
each of these mutually exclusive hypotheses.
-/
theorem quadratic_ge_of_selected (n : ℕ) (x : E)
    (hx : ∀ i ∉ spectralSelected D.summable (n+1), inner ℝ (D.basis i) x = 0) :
    D.eigenvalue n * ‖x‖^2 ≤ inner ℝ x (T x) := by
  -- Separate `i ∈ spectralSelected D.summable (n+1)` from its negation; prove the goal under
  -- each of these mutually exclusive hypotheses.
  have h₁ := (basis_hasSum_sq D.basis x).mul_left (D.eigenvalue n)
  have h₂ := eigenbasis_quadratic_hasSum D.basis T D.equation x
  apply hasSum_le _ h₁ h₂
  intro i
  by_cases hi : i ∈ spectralSelected D.summable (n+1)
  · have hle : D.eigenvalue n ≤ D.eig i := by
      cases h : spectralNext D.summable (spectralSelected D.summable n) with
      | none =>
        simp only [eigenvalue,spectralSorted,h,Option.elim_none]
        exact D.nonneg i
      | some j =>
        rw [eigenvalue,spectralSorted_eq D.summable h]
        rw [spectralSelected,h] at hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact le_rfl
        · exact spectralSelected_ge_missing D.summable n (spectralNext_some D.summable h).1 i hi
    exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)
  · simp only [hx i hi,zero_pow (by norm_num : (2:ℕ) ≠ 0),mul_zero,le_refl]

end PositiveSpectralData
end
end chebyshev2.Continuum
