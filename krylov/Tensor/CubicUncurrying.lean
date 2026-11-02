import krylov.Tensor.CubicMultilinear

/-!
Article: main_krylov, thm:Hp, the reverse genuine cubic dictionary.
Use: admit explicit symmetric cubic witnesses to the same actual
multilinear spectral ball used in the nuclear amplification theorem.
Source: mathlib's continuous multilinear currying equivalences.
-/

namespace krylov.Tensor
noncomputable section
open krylov.Functions
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine three-slot continuous multilinear map of a curried cubic.
Article: main_krylov, thm:Hp. -/
def cubicUncurried (T : SymmetricCubic E) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ :=
  let c₁ := (continuousMultilinearCurryFin1 ℝ E ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let c₂ := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => E) ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap
  (c₂.comp ((c₁.postcomp E).comp T.form)).uncurryLeft

/-- Uncurrying preserves the exact three actual arguments.
Article: main_krylov, thm:Hp. Proof: the actual isometric evaluation formulas. -/
theorem cubicUncurried_apply (T : SymmetricCubic E) (v : Fin 3 → E) :
    cubicUncurried T v = T.form (v 0) (v 1) (v 2) := rfl

/-- Every explicit symmetric curried cubic is genuinely invariant under all slot permutations.
Article: main_krylov, thm:Hp.
Proof: the two defining transpositions generate the six permutations of three slots. -/
theorem cubicUncurried_symmetric (T : SymmetricCubic E) : IsSymmetricForm (cubicUncurried T) := by
  intro σ
  ext v
  change T.form (v (σ 0)) (v (σ 1)) (v (σ 2)) = T.form (v 0) (v 1) (v 2)
  have h₀₁ : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
  have h₀₂ : σ 0 ≠ σ 2 := σ.injective.ne (by decide)
  have h₁₂ : σ 1 ≠ σ 2 := σ.injective.ne (by decide)
  generalize h₀ : σ 0 = a at *
  generalize h₁ : σ 1 = b at *
  generalize h₂ : σ 2 = c at *
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp_all only [Fin.zero_eta, Fin.isValue, Fin.mk_one, ne_eq, not_true_eq_false,
      T.swap₁, T.swap₂]
  all_goals
    exact (T.swap₁ (v 2) (v 1) (v 0)).trans
      ((T.swap₂ (v 1) (v 2) (v 0)).trans (T.swap₁ (v 1) (v 0) (v 2)))

/-- Explicit curried cubic witnesses satisfy exactly the same original diagonal budget.
Article: main_krylov, thm:Hp.
Proof: the true diagonal evaluation is preserved by uncurrying. -/
theorem cubicUncurried_diagonal_bound (T : SymmetricCubic E) {C : ℝ}
    (h : ∀ x : E, ‖x‖ = 1 → |T.form x x x| ≤ C) :
    ∀ x : E, ‖x‖ = 1 → |cubicUncurried T (fun _ : Fin 3 => x)| ≤ C := h

end
end krylov.Tensor
