import polyak.Interpolation.Extension
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Article: finite-dimensional consequences of Theorem interpolation.
Use: Euclidean realizations, including zero dimension, and explicit confirmation
that the global construction permits an unbounded divergent sample sequence.
-/

noncomputable section

namespace polyak.Interpolation

/-- Article: finite-dimensional specialization of interpolation.
Use: genuine Euclidean-space realizations with no boundedness restriction on the table.
Proof: specialize the Hilbert-space theorem; the index type remains arbitrary. -/
theorem euclidean_interpolation_iff {I : Type*} {n : ℕ}
    {x σ : I → EuclideanSpace ℝ (Fin n)} {values : I → ℝ} (star : I)
    (hx : x star = 0) (hσ : σ star = 0) (hvalues : values star = 0) :
    (∃ ψ : EuclideanSpace ℝ (Fin n) → ℝ, polyak.NormalizedSmooth ψ ∧
      ∀ i, ψ (x i) = values i ∧ gradient ψ (x i) = σ i) ↔
      TableFeasible x σ values := interpolation_iff star hx hσ hvalues

/-- Article: arbitrary unbounded sets of data in Theorem interpolation.
Use: a divergent sequence is covered by the global construction itself.
Proof: the zero-gradient table is feasible on every nonnegative integer,
then use interpolation and the Archimedean property to certify unboundedness. -/
theorem exists_interpolant_unbounded_sequence :
    ∃ ψ : ℝ → ℝ, polyak.NormalizedSmooth ψ ∧
      (∀ n : ℕ, ψ n = 0 ∧ gradient ψ n = 0) ∧
      ∀ R : ℝ, ∃ n : ℕ, R < ‖(n : ℝ)‖ := by
  have htable : TableFeasible (fun n : ℕ => (n : ℝ)) (fun _ => 0) (fun _ => 0) := by
    intro i j
    simp only [datumT, datumR, zero_add, inner_zero_left, mul_zero, sub_zero,
      sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), abs_zero]
    positivity
  obtain ⟨ψ, hψ, hdata⟩ := exists_normalized_interpolant htable 0 (by simp) rfl rfl
  refine ⟨ψ, hψ, hdata, fun R => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_gt R
  exact ⟨n, by simpa [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)] using hn⟩

end polyak.Interpolation
