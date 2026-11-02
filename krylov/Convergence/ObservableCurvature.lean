import krylov.Convergence.ObservableEnergy

/-!
Article: main_krylov, apG:Dunif, actual searched-energy denominators.
Use: derive the true scalar line-energy interval from the real averaged
Hessian error, before interpreting the observed square-root energy ratio.
Source: the real operator norm and Cauchy--Schwarz, including zero vectors.
-/
namespace krylov.Convergence
noncomputable section
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A true averaged-Hessian operator error bounds its genuine quadratic
curvature on both sides. Article: main_krylov, apG:Dunif. -/
theorem observable_operator_form (A : E →L[ℝ] E) (epsilon : ℝ)
    (hA : ‖A-ContinuousLinearMap.id ℝ E‖≤epsilon) (v : E) :
    (1-epsilon)*‖v‖^2 ≤ inner ℝ v (A v) ∧
      inner ℝ v (A v)≤(1+epsilon)*‖v‖^2 := by
  have hn := norm_inner_le_norm (𝕜:=ℝ) v ((A-ContinuousLinearMap.id ℝ E) v)
  have ho := ((A-ContinuousLinearMap.id ℝ E).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right hA (norm_nonneg v))
  have hh := hn.trans (mul_le_mul_of_nonneg_left ho (norm_nonneg v))
  rw [Real.norm_eq_abs,_root_.sub_apply,ContinuousLinearMap.id_apply,inner_sub_right,
    real_inner_self_eq_norm_sq] at hh
  exact ⟨by nlinarith only [(abs_le.mp hh).1],by nlinarith only [(abs_le.mp hh).2]⟩

end
end krylov.Convergence
