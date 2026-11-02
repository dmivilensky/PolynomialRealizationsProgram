import krylov.Nonlinear.GradientExtension
import Mathlib.Analysis.Calculus.MeanValue

/-!
Article: main_krylov, thm:RFCS, local genuine gradient-model control.
Use: Derive small local Lipschitz gradient error from actual continuous
Hessians and bound the real normalized initial gradient after cycle scaling.
Source: mathlib's derivative mean-value theorem on convex sets, genuine
Fréchet derivatives and exact linear model homogeneity.
-/

namespace krylov.Nonlinear
noncomputable section
open Set Filter Topology Metric
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An actual Hessian perturbation bound on a convex domain gives the same Lipschitz bound for the genuine gradient error around its fixed linear model.
Use: Derive gradient-error control from real Hessian data before extending the nonlinear oracle.
Article: main_krylov, thm:RFCS, local true gradient and Hessian control.
Proof: Subtract the true derivative of the fixed linear model and apply the proved convex derivative mean-value theorem.
-/
theorem gradient_error_lipschitzOn_of_hessian (G : E → E) (H : E → E →L[ℝ] E)
    (Q : E →L[ℝ] E) (S : Set E) (hS : Convex ℝ S) {η : ℝ≥0}
    (hG : ∀ x∈S, HasFDerivAt G (H x) x) (hH : ∀ x∈S, ‖H x-Q‖≤(η : ℝ)) :
    LipschitzOnWith η (fun x => G x-Q x) S := by
  apply Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun x hx => ((hG x hx).sub Q.hasFDerivAt).hasFDerivWithinAt) _ hS
  intro x hx
  exact_mod_cast hH x hx

/-- Continuity of the actual Hessian at its fixed model gives arbitrarily small genuine gradient-error Lipschitz constants on sufficiently small physical balls.
Use: Choose a genuine local oracle-extension domain before all nonlinear RFC-S queries.
Article: main_krylov, thm:RFCS, local true gradient and Hessian control.
Proof: Intersect the derivative neighborhood with the Hessian continuity neighborhood, then apply the real convex mean-value estimate.
-/
theorem exists_gradient_error_lipschitz_ball (G : E → E) (H : E → E →L[ℝ] E)
    (Q : E →L[ℝ] E) (hQ : H 0=Q) (hH : ContinuousAt H 0)
    (hG : ∀ᶠ x in 𝓝 (0 : E), HasFDerivAt G (H x) x) (η : ℝ≥0) (hη : 0<η) :
    ∃ r : ℝ, 0<r ∧ LipschitzOnWith η (fun x => G x-Q x) (ball 0 r) := by
  have hc : ContinuousAt (fun x => ‖H x-Q‖) 0 := (hH.sub continuousAt_const).norm
  have hz : ‖H 0-Q‖=0 := by rw [hQ,sub_self,norm_zero]
  have hlt : ‖H 0-Q‖<(η : ℝ) := by rw [hz]; exact_mod_cast hη
  have he : ∀ᶠ x in 𝓝 (0 : E), HasFDerivAt G (H x) x ∧ ‖H x-Q‖≤(η : ℝ) := by
    filter_upwards [hG,hc.eventually (gt_mem_nhds hlt)] with x hd hx
    exact ⟨hd,hx.le⟩
  obtain ⟨r,hr,hbound⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨r,hr,gradient_error_lipschitzOn_of_hessian G H Q (ball 0 r) (convex_ball 0 r)
    (fun x hx => (hbound hx).1) (fun x hx => (hbound hx).2)⟩

/-- The normalized genuine initial gradient differs from its original quadratic reference by at most the model-error Lipschitz constant times the initial direction norm.
Use: Discharge the true initial-gradient tube condition from the actual local gradient model.
Article: main_krylov, thm:RFCS, local true gradient and Hessian control.
Proof: Compare the genuine error to its zero value at the minimizer and cancel the positive cycle scale.
-/
theorem normalized_gradient_error_le (G : E → E) (Q : E →L[ℝ] E) (h₀ : G 0=0)
    {η : ℝ≥0} (hG : LipschitzWith η (fun x => G x-Q x)) (u : E) {ε : ℝ} (hε : 0<ε) :
    ‖ε⁻¹ • G (ε • u)-Q u‖≤(η : ℝ)*‖u‖ := by
  have h := hG.norm_sub_le (ε • u) 0
  simp only [h₀,map_zero,sub_zero,norm_smul,Real.norm_of_nonneg hε.le] at h
  have he : ε⁻¹ • G (ε • u)-Q u=ε⁻¹ • (G (ε • u)-Q (ε • u)) := by
    rw [smul_sub,map_smul,smul_smul,inv_mul_cancel₀ hε.ne',one_smul]
  rw [he,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hε.le)]
  calc
    _ ≤ ε⁻¹*((η : ℝ)*(ε*‖u‖)) := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hε.le)
    _ = (η : ℝ)*‖u‖ := by field_simp

end
end krylov.Nonlinear
