import krylov.Nonlinear.GradientQuadratic
import krylov.Nonlinear.CanonicalAverages

/-!
Article: main_krylov, thm:RFCS, actual canonical gradient/error comparison.
Use: Derive genuine quadratic and scale-relative canonical gradient/error
mismatch bounds from the original real local Hessian and fixed metric model.
Source: actual gradient Taylor error, true continuous linear metric inverse
and exact model normalization. No error/gradient comparison is assumed.
-/

namespace krylov.Nonlinear
noncomputable section
open Set
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The actual canonical gradient/error mismatch has the genuine physical gradient Taylor bound multiplied only by the fixed inverse metric norm.
Use: Relate actual function error to the true normalized measured gradient.
Article: main_krylov, thm:RFCS, true canonical gradient/error transfer.
Proof: Apply the actual quadratic gradient-model estimate, normalize by the true inverse coordinate map and cancel the genuine quadratic model action.
-/
theorem coordinate_gradient_error_bound (T : E ≃L[ℝ] E) (G : E → E) (H : E → E →L[ℝ] E)
    (Q : E →L[ℝ] E) (hQ : ∀ v, T.symm (Q v)=T v)
    (S : Set E) (hS : Convex ℝ S) (h₀ : (0 : E)∈S) (hG₀ : G 0=0) (hH₀ : H 0=Q)
    {L : ℝ≥0} (hH : LipschitzOnWith L H S) (hG : ∀ x∈S, HasFDerivAt G (H x) x)
    (x : E) (hx : x∈S) :
    ‖T x-T.symm (G x)‖≤(‖T.symm.toContinuousLinearMap‖*(L : ℝ)/2)*‖x‖^2 := by
  have hb := gradient_model_quadratic_error G H Q S hS h₀ hH₀ hH hG x hx
  rw [hG₀,sub_zero] at hb
  have hn := T.symm.toContinuousLinearMap.le_opNorm (G x-Q x)
  simp only [map_sub,ContinuousLinearEquiv.coe_coe,hQ] at hn
  rw [norm_sub_rev]
  exact hn.trans ((mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans_eq (by ring))

/-- A true physical output-size bound gives a genuine small relative canonical gradient/error mismatch with the explicit fixed metric coefficient.
Use: Discharge the actual relative comparison needed to preserve the sharp last-probe leading coefficient in the error norm.
Article: main_krylov, thm:RFCS, true canonical gradient/error transfer.
Proof: Use the genuine quadratic canonical gradient/error bound and bound its two physical displacement factors separately by the actual cycle size and the actual inverse-metric image of the canonical error.
-/
theorem coordinate_gradient_relative_error (T : E ≃L[ℝ] E) (G : E → E) (H : E → E →L[ℝ] E)
    (Q : E →L[ℝ] E) (hQ : ∀ v, T.symm (Q v)=T v)
    (S : Set E) (hS : Convex ℝ S) (h₀ : (0 : E)∈S) (hG₀ : G 0=0) (hH₀ : H 0=Q)
    {L : ℝ≥0} (hH : LipschitzOnWith L H S) (hG : ∀ x∈S, HasFDerivAt G (H x) x)
    (x : E) (hx : x∈S) {D ε : ℝ} (hD : 0≤D) (hε : 0≤ε) (hsize : ‖x‖≤ε*D) :
    ‖T x-T.symm (G x)‖≤(‖T.symm.toContinuousLinearMap‖^2*(L : ℝ)*D/2)*ε*‖T x‖ := by
  have hb := coordinate_gradient_error_bound T G H Q hQ S hS h₀ hG₀ hH₀ hH hG x hx
  have hinv : ‖x‖≤‖T.symm.toContinuousLinearMap‖*‖T x‖ := by
    simpa only [ContinuousLinearEquiv.coe_coe,T.symm_apply_apply] using T.symm.toContinuousLinearMap.le_opNorm (T x)
  have hsq : ‖x‖^2≤(ε*D)*(‖T.symm.toContinuousLinearMap‖*‖T x‖) := by
    simpa only [pow_two] using mul_le_mul hsize hinv (norm_nonneg x) (mul_nonneg hε hD)
  exact hb.trans ((mul_le_mul_of_nonneg_left hsq (by positivity : 0≤‖T.symm.toContinuousLinearMap‖*(L : ℝ)/2)).trans_eq (by ring))

end
end krylov.Nonlinear
