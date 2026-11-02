import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Tactic

/-!
Article: main_krylov, Appendix A, apA:galerkin(b), symmetric uncertainty.
Use: construct actual self-adjoint uncertainty operators with a prescribed image;
the operator norm here is the continuous-linear-map norm on the Hilbert space.
Source: Rump03, Lemma 5.1; mathlib's orthogonal reflection supplies the witness.
-/

namespace krylov.LinearAlgebra
noncomputable section
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- An orthogonal reflection is a self-adjoint contraction.
Use: the symmetric uncertainty witness is a nonnegative multiple of a reflection.
Article: main_krylov, apA:galerkin(b).
Source: mathlib Submodule.reflection and its involutive isometry identities.
Proof: apply preservation of inner products with the reflected second argument. -/
theorem reflection_selfAdjoint (K : Submodule ℝ E) [K.HasOrthogonalProjection] :
    IsSelfAdjoint K.reflection.toLinearIsometry.toContinuousLinearMap := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change inner ℝ (K.reflection x) y = inner ℝ x (K.reflection y)
  simpa only [Submodule.reflection_reflection] using
    K.reflection.inner_map_map x (K.reflection y)

/-- Every point in the uncertainty ball is attained by a self-adjoint operator.
Use: establishes attainability rather than only the easy operator-norm upper bound.
Article: main_krylov, apA:galerkin(b), {Tv : T=T*, ‖T‖≤Ω} is the full ball.
Source: Rump03, Lemma 5.1.
Proof: reflect v to the direction of w and scale by the required norm ratio;
zero vectors are handled separately so every division has a nonzero denominator. -/
theorem exists_selfAdjoint_image (v w : E) {Ω : ℝ} (hΩ : 0 ≤ Ω)
    (hw : ‖w‖ ≤ Ω * ‖v‖) :
    ∃ T : E →L[ℝ] E, IsSelfAdjoint T ∧ ‖T‖ ≤ Ω ∧ T v = w := by
  by_cases hv : v = 0
  · have hw0 : w = 0 := norm_eq_zero.mp (le_antisymm (by simpa [hv] using hw) (norm_nonneg _))
    exact ⟨0, IsSelfAdjoint.zero _, by simpa using hΩ, by simp [hw0]⟩
  by_cases hw0 : w = 0
  · exact ⟨0, IsSelfAdjoint.zero _, by simpa using hΩ, by simp [hw0]⟩
  -- Normalize the target to the same sphere as v before applying a genuine isometry.
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  let u := (‖v‖ / ‖w‖) • w
  have hu : ‖u‖ = ‖v‖ := by
    change ‖(‖v‖ / ‖w‖) • w‖ = ‖v‖
    rw [norm_smul, Real.norm_of_nonneg (div_nonneg hvn.le hwn.le),
      div_mul_cancel₀ _ hwn.ne']
  let K := (ℝ ∙ (v - u))ᗮ
  let R := K.reflection.toLinearIsometry.toContinuousLinearMap
  have hRv : R v = u := Submodule.reflection_sub hu.symm
  have hR : IsSelfAdjoint R := reflection_selfAdjoint K
  refine ⟨(‖w‖ / ‖v‖) • R, ?_, ?_, ?_⟩
  · exact IsSelfAdjoint.smul (show IsSelfAdjoint (‖w‖ / ‖v‖) from rfl) hR
  · calc
      ‖(‖w‖ / ‖v‖) • R‖ = (‖w‖ / ‖v‖) * ‖R‖ := by
        rw [norm_smul, Real.norm_of_nonneg (div_nonneg hwn.le hvn.le)]
      _ ≤ (‖w‖ / ‖v‖) * 1 := mul_le_mul_of_nonneg_left
        K.reflection.toLinearIsometry.norm_toContinuousLinearMap_le (div_nonneg hwn.le hvn.le)
      _ ≤ Ω := by simpa using (div_le_iff₀ hvn).mpr hw
  · change (‖w‖ / ‖v‖) • R v = w
    rw [hRv]
    change (‖w‖ / ‖v‖) • ((‖v‖ / ‖w‖) • w) = w
    rw [smul_smul]
    have hc : ‖w‖ / ‖v‖ * (‖v‖ / ‖w‖) = 1 := by field_simp
    rw [hc, one_smul]

/-- The image of the self-adjoint operator ball equals the ordinary Hilbert ball.
Use: provides the exact information set used by robust residual minimization.
Article: main_krylov, apA:galerkin(b), symmetric-ball identity.
Proof: combine the constructed reflection witness with the operator-norm estimate. -/
theorem selfAdjoint_image_iff (v w : E) {Ω : ℝ} (hΩ : 0 ≤ Ω) :
    (∃ T : E →L[ℝ] E, IsSelfAdjoint T ∧ ‖T‖ ≤ Ω ∧ T v = w) ↔ ‖w‖ ≤ Ω * ‖v‖ := by
  constructor
  · rintro ⟨T, _, hT, rfl⟩
    exact (T.le_opNorm v).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
  · exact exists_selfAdjoint_image v w hΩ

omit [CompleteSpace E] in

/-- The robust residual has the printed universal upper bound.
Use: bounds every admissible symmetric perturbation, including zero budgets.
Article: main_krylov, apA:galerkin(b), the robust least-squares maximum.
Proof: combine the triangle inequality with the actual operator-norm estimate. -/
theorem symmetric_residual_le (a v : E) {Ω : ℝ} (T : E →L[ℝ] E) (hT : ‖T‖ ≤ Ω) :
    ‖a + T v‖ ≤ ‖a‖ + Ω * ‖v‖ := by
  exact (norm_add_le _ _).trans (add_le_add le_rfl
    ((T.le_opNorm v).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))))

/-- A self-adjoint perturbation attains the robust residual bound exactly.
Use: proves that the robust least-squares upper bound is an actual maximum.
Article: main_krylov, apA:galerkin(b), max_T ‖a+Tv‖ = ‖a‖+Ω‖v‖.
Proof: align the attainable ball image with a; if a vanishes use the image Ωv. -/
theorem symmetric_residual_attained (a v : E) {Ω : ℝ} (hΩ : 0 ≤ Ω) :
    ∃ T : E →L[ℝ] E, IsSelfAdjoint T ∧ ‖T‖ ≤ Ω ∧
      ‖a + T v‖ = ‖a‖ + Ω * ‖v‖ := by
  -- Align the attainable image with the residual, handling a zero residual separately.
  by_cases ha : a = 0
  · obtain ⟨T, hTs, hT, hv⟩ := exists_selfAdjoint_image v (Ω • v) hΩ (by
      rw [norm_smul, Real.norm_of_nonneg hΩ])
    exact ⟨T, hTs, hT, by simp only [ha, zero_add, norm_zero, hv, norm_smul,
      Real.norm_of_nonneg hΩ]⟩
  have han : 0 < ‖a‖ := norm_pos_iff.mpr ha
  let c := Ω * ‖v‖ / ‖a‖
  have hc : 0 ≤ c := div_nonneg (mul_nonneg hΩ (norm_nonneg _)) han.le
  have hnorm : ‖c • a‖ = Ω * ‖v‖ := by
    rw [norm_smul, Real.norm_of_nonneg hc]
    exact div_mul_cancel₀ _ han.ne'
  obtain ⟨T, hTs, hT, hv⟩ := exists_selfAdjoint_image v (c • a) hΩ hnorm.le
  refine ⟨T, hTs, hT, ?_⟩
  rw [hv, show a + c • a = (1 + c) • a by simp only [add_smul, one_smul],
    norm_smul, Real.norm_of_nonneg (by linarith : 0 ≤ 1 + c)]
  have he : c * ‖a‖ = Ω * ‖v‖ := div_mul_cancel₀ _ han.ne'
  nlinarith

/-- The robust symmetric uncertainty value is an actual maximum over admissible operators.
Use: a quantified maximum statement for arbitrary linear prediction operators N.
Article: main_krylov, apA:galerkin(b), robust least-squares equality.
Proof: combine the universal bound and the explicitly attained symmetric witness. -/
theorem robust_residual_isGreatest (ρ b : E) (N : E →L[ℝ] E) {Ω : ℝ} (hΩ : 0 ≤ Ω) :
    IsGreatest {r : ℝ | ∃ T : E →L[ℝ] E,
      IsSelfAdjoint T ∧ ‖T‖ ≤ Ω ∧ r = ‖ρ + N b + T b‖}
      (‖ρ + N b‖ + Ω * ‖b‖) := by
  obtain ⟨T, hTs, hT, he⟩ := symmetric_residual_attained (ρ + N b) b hΩ
  refine ⟨⟨T, hTs, hT, he.symm⟩, ?_⟩
  rintro r ⟨U, _, hU, rfl⟩
  exact symmetric_residual_le (ρ + N b) b U hU

omit [CompleteSpace E] in
/-- At the critical radius every point of the central correction segment is optimal.
Use: includes the whole nonunique transition case rather than only its endpoints.
Article: main_krylov, apA:galerkin(b), Ω = 1 minimizers [−ρ,0].
Source: mathlib dist_add_dist_eq_iff in a strictly convex real normed space.
Proof: rewrite the objective equality as equality in the triangle inequality. -/
theorem robust_identity_critical_iff (ρ b : E) :
    ‖ρ + b‖ + ‖b‖ = ‖ρ‖ ↔ b ∈ segment ℝ (-ρ) 0 := by
  rw [mem_segment_iff_wbtw, ← dist_add_dist_eq_iff]
  simp only [dist_eq_norm, sub_zero, show -ρ - b = -(ρ + b) by abel, norm_neg]

omit [CompleteSpace E] [InnerProductSpace ℝ E]

/-- The robust identity-model objective has the sharp global lower value.
Use: selects correction or no correction according to the uncertainty radius.
Article: main_krylov, apA:galerkin(b), min_b ‖ρ+b‖+Ω‖b‖ = min(1,Ω)‖ρ‖.
Proof: multiply the triangle inequality by the smaller of one and Ω. -/
theorem robust_identity_lower (ρ b : E) {Ω : ℝ} (hΩ : 0 ≤ Ω) :
    min 1 Ω * ‖ρ‖ ≤ ‖ρ + b‖ + Ω * ‖b‖ := by
  -- Keep the nonnegative residual and step costs separate in the two radius regimes.
  have h := norm_sub_le (ρ + b) b
  rw [add_sub_cancel_right] at h
  have hn := norm_nonneg (ρ + b)
  have hb := norm_nonneg b
  by_cases ho : Ω ≤ 1
  · rw [min_eq_right ho]
    nlinarith [mul_le_mul_of_nonneg_left h hΩ]
  · rw [min_eq_left (le_of_not_ge ho)]
    nlinarith

/-- Below radius one the unique robust minimizer is the full central correction.
Use: the strict small-uncertainty regime of the correction decision.
Article: main_krylov, apA:galerkin(b), Ω < 1 equality case.
Proof: the residual term has strictly positive surplus coefficient 1−Ω. -/
theorem robust_identity_small_iff (ρ b : E) {Ω : ℝ} (hΩ : 0 ≤ Ω) (ho : Ω < 1) :
    ‖ρ + b‖ + Ω * ‖b‖ = Ω * ‖ρ‖ ↔ b = -ρ := by
  -- Equality leaves no positive residual cost when the uncertainty radius is strictly below one.
  constructor
  · intro he
    have h := norm_sub_le (ρ + b) b
    rw [add_sub_cancel_right] at h
    have hz : ‖ρ + b‖ = 0 := by
      nlinarith [mul_le_mul_of_nonneg_left h hΩ, norm_nonneg (ρ + b)]
    exact eq_neg_of_add_eq_zero_right (norm_eq_zero.mp hz)
  · rintro rfl
    simp

/-- Above radius one the unique robust minimizer takes no correction.
Use: the strict large-uncertainty regime of the correction decision.
Article: main_krylov, apA:galerkin(b), Ω > 1 equality case.
Proof: the coefficient Ω−1 leaves a strictly positive cost on every nonzero update. -/
theorem robust_identity_large_iff (ρ b : E) {Ω : ℝ} (ho : 1 < Ω) :
    ‖ρ + b‖ + Ω * ‖b‖ = ‖ρ‖ ↔ b = 0 := by
  constructor
  · intro he
    have h := norm_sub_le (ρ + b) b
    rw [add_sub_cancel_right] at h
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg b])
  · rintro rfl
    simp

/-- The robust identity-model objective has its exact attained minimum.
Use: completes the minimax value and complements the classified equality cases.
Article: main_krylov, apA:galerkin(b), the minimum min(1,Ω)‖ρ‖.
Proof: use the full correction below radius one and the zero correction above it. -/
theorem robust_identity_isLeast (ρ : E) {Ω : ℝ} (hΩ : 0 ≤ Ω) :
    IsLeast (Set.range (fun b : E => ‖ρ + b‖ + Ω * ‖b‖)) (min 1 Ω * ‖ρ‖) := by
  constructor
  · by_cases ho : Ω ≤ 1
    · exact ⟨-ρ, by simp only [add_neg_cancel, norm_zero, zero_add, norm_neg, min_eq_right ho]⟩
    · exact ⟨0, by simp only [add_zero, norm_zero, mul_zero, min_eq_left (le_of_not_ge ho), one_mul]⟩
  · rintro r ⟨b, rfl⟩
    exact robust_identity_lower ρ b hΩ

end
end krylov.LinearAlgebra
