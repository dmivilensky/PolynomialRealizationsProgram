import krylov.Nonlinear.AveragedComparison

/-!
Article: main_krylov, thm:RFCS, genuine initial-gradient second-order control.
Use: Derive the actual quadratic gradient-model error and its normalized
cycle form from the original local Lipschitz Hessian.
Source: the reused exact averaged-derivative FTC and its proved one-half
segment Lipschitz bound, with genuine convex domain enclosure.
-/

namespace krylov.Nonlinear
noncomputable section
open Set chebyshev1.Nonlinear
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
open scoped NNReal

/-- The genuine gradient error around its true Hessian at the minimizer is bounded by one half of the actual Hessian Lipschitz constant times the squared displacement.
Use: Derive the real initial-gradient source drift from local function data.
Article: main_krylov, thm:RFCS, true nonlinear initial-gradient source control.
Proof: Use the genuine averaged-Hessian FTC on the enclosed radial segment, then apply its exact one-half norm bound to the original displacement.
-/
theorem gradient_model_quadratic_error (G : E → E) (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E)
    (S : Set E) (hS : Convex ℝ S) (h₀ : (0 : E)∈S) (hH₀ : H 0=Q)
    {L : ℝ≥0} (hH : LipschitzOnWith L H S) (hG : ∀ x∈S, HasFDerivAt G (H x) x)
    (x : E) (hx : x∈S) : ‖G x-G 0-Q x‖≤(L : ℝ)/2*‖x‖^2 := by
  have hp t (ht : t∈Icc (0 : ℝ) 1) : (0 : E)+t • x∈S :=
    hS.add_smul_mem h₀ (by simpa only [zero_add] using hx) ht
  have ha := hH.continuousOn.comp (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hp
  have he := averagedDerivative_apply G H 0 x ha (fun t ht => hG _ (hp t ht))
  simp only [zero_add] at he
  have hb := averagedDerivative_sub_norm_le H 0 x L ha (fun t ht => by
    have hh := hH.norm_sub_le (hp t ht) h₀
    simpa only [zero_add,sub_zero] using hh)
  rw [hH₀] at hb
  have hid : G x-G 0-Q x=(averagedDerivative H 0 x-Q) x := by
    rw [_root_.sub_apply,he]
  rw [hid]
  exact ((averagedDerivative H 0 x-Q).le_opNorm x).trans
    ((mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans_eq (by ring))

/-- The actual scaled initial gradient differs from the original quadratic reference by at most one half of the real Hessian Lipschitz constant times the cycle scale and squared initial direction norm.
Use: Obtain a genuine source perturbation proportional to the nonlinear cycle size.
Article: main_krylov, thm:RFCS, true nonlinear initial-gradient source control.
Proof: Apply the actual quadratic gradient-model bound at the true scaled initial point and cancel the positive scale in its genuine measured gradient difference.
-/
theorem normalized_gradient_quadratic_error (G : E → E) (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E)
    (S : Set E) (hS : Convex ℝ S) (h₀ : (0 : E)∈S) (hG₀ : G 0=0) (hH₀ : H 0=Q)
    {L : ℝ≥0} (hH : LipschitzOnWith L H S) (hG : ∀ x∈S, HasFDerivAt G (H x) x)
    (u : E) {ε : ℝ} (hε : 0<ε) (hx : ε • u∈S) :
    ‖ε⁻¹ • G (ε • u)-Q u‖≤(L : ℝ)/2*ε*‖u‖^2 := by
  have hb := gradient_model_quadratic_error G H Q S hS h₀ hH₀ hH hG (ε • u) hx
  rw [hG₀,sub_zero,norm_smul,Real.norm_of_nonneg hε.le] at hb
  have he : ε⁻¹ • G (ε • u)-Q u=ε⁻¹ • (G (ε • u)-Q (ε • u)) := by
    rw [smul_sub,map_smul,smul_smul,inv_mul_cancel₀ hε.ne',one_smul]
  rw [he,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hε.le)]
  calc
    _ ≤ ε⁻¹*((L : ℝ)/2*(ε*‖u‖)^2) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hε.le)
    _ = _ := by field_simp

end
end krylov.Nonlinear
