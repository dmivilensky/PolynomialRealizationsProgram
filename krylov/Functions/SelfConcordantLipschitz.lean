import krylov.Functions.SelfConcordantMetric
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
Article: main_krylov, apG:sc(iii), the printed sharp Hessian Lipschitz constant.
Use: convert the proved metric sandwich into the genuine local constant
2(1-R)^(-3), rather than assuming a Hessian norm bound or a Lipschitz constant.
Source: Nesterov18, Lemma 5.1.2 and Theorem 5.1.7; mathlib's self-adjoint
Rayleigh quotient formula and convex derivative mean value theorem.
-/

namespace krylov.Functions
noncomputable section
open Set Metric
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A self-adjoint nonnegative quadratic-form upper bound controls the true operator norm.
Article: main_krylov, apG:sc(iii).
Proof: divide each actual Rayleigh quotient by the squared norm and use the
library's exact self-adjoint operator norm identity; zero vectors are separate. -/
theorem symmetric_norm_le_of_quadratic (A : E →L[ℝ] E) (hA : A.IsSymmetric)
    {C : ℝ} (hC : 0 ≤ C) (hn : ∀ v : E, 0 ≤ inner ℝ v (A v))
    (hb : ∀ v : E, inner ℝ v (A v) ≤ C * ‖v‖ ^ 2) : ‖A‖ ≤ C := by
  rw [A.norm_eq_iSup_rayleighQuotient hA]
  apply ciSup_le
  intro v
  by_cases hv : v = 0
  · simpa [hv] using hC
  · have hd : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
    simp only [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
      RCLike.re_to_real]
    rw [real_inner_comm v (A v)]
    rw [abs_of_nonneg (div_nonneg (hn v) hd.le)]
    exact (div_le_iff₀ hd).mpr (hb v)

variable [CompleteSpace E]

/-- Genuine standard self-concordant scalar functions have the sharp printed Hessian Lipschitz constant.
Article: main_krylov, apG:sc(iii).
Proof: the proved metric comparison bounds each real Hessian norm by
(1-R)^(-2); the original mixed self-concordance inequality then bounds the
actual Hessian derivative by 2(1-R)^(-3). Integrate on the convex ball. -/
theorem standardSelfConcordant_hessian_lipschitz (f : E → ℝ) (U : Set E)
    (D : krylov.Nonlinear.StandardSelfConcordantData f U)
    (h₀ : (0 : E) ∈ U) (hH₀ : D.hessian 0 = ContinuousLinearMap.id ℝ E)
    {R : ℝ} (hR1 : R < 1) (hsub : ball (0 : E) R ⊆ U) :
    LipschitzOnWith (Real.toNNReal (2 * (1 - R)⁻¹ ^ 3)) D.hessian (ball 0 R) := by
  apply Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun x hx => (D.hessian_derivative x (hsub hx)).hasFDerivWithinAt) _ (convex_ball 0 R)
  intro x hx
  have hxR : ‖x‖ < R := mem_ball_zero_iff.mp hx
  have hx1 : ‖x‖ < 1 := hxR.trans hR1
  have hscalar : (1 - ‖x‖)⁻¹ ≤ (1 - R)⁻¹ := by
    exact inv_anti₀ (sub_pos.mpr hR1) (by linarith)
  have hnorm : ‖D.hessian x‖ ≤ ((1 - R)⁻¹) ^ 2 := by
    apply symmetric_norm_le_of_quadratic (D.hessian x) (D.hessian_symmetric x (hsub hx))
      (sq_nonneg _) (D.hessian_nonnegative x (hsub hx))
    intro v
    have hb := (standardSelfConcordant_metric f U D h₀ hH₀ x (hsub hx) hx1 v).2
    apply hb.trans
    gcongr
  have hb := krylov.Nonlinear.selfConcordant_mixed_derivative_norm_le
    (D.hessian x) (D.variation x) (D.mixed x (hsub hx))
    (inv_nonneg.mpr (sub_pos.mpr hR1).le) hnorm
  rw [← Real.coe_toNNReal (2 * (1 - R)⁻¹ ^ 3) (by positivity)] at hb
  exact_mod_cast hb

end
end krylov.Functions
