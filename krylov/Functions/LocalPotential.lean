import krylov.Nonlinear.GradientQuadratic
import krylov.Functions.SegmentTrapezoid

/-!
Article: main_krylov, apG:E, genuine local quadratic comparison of function values.
Use: obtain the sharp cubic potential remainder from the actual gradient and its
Lipschitz Hessian, before constructing the local exact line search.
Source: the fundamental theorem of calculus and the reused sharp gradient
Taylor estimate. The Hessian and gradient are actual derivatives throughout.
-/

namespace krylov.Functions
noncomputable section
open Set MeasureTheory InnerProductSpace
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual potential has cubic Taylor error with the sharp constant one sixth.
Article: main_krylov, apG:E.
Proof: integrate the genuine gradient error along the radial segment; its
quadratic radial weight has integral one third. -/
theorem potential_quadratic_error (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) (S : Set E) (hS : Convex ℝ S) (h₀ : (0 : E) ∈ S)
    (hG₀ : G 0 = 0) (hH₀ : H 0 = ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hH : LipschitzOnWith L H S)
    (hF : ∀ x ∈ S, HasFDerivAt f (innerSL ℝ (G x)) x)
    (hG : ∀ x ∈ S, HasFDerivAt G (H x) x) (y : E) (hy : y ∈ S) :
    |f y - f 0 - ‖y‖ ^ 2 / 2| ≤ (L : ℝ) * ‖y‖ ^ 3 / 6 := by
  have hp t (ht : t ∈ Icc (0 : ℝ) 1) : t • y ∈ S := by
    simpa only [zero_add] using hS.add_smul_mem h₀ (by simpa using hy) ht
  let F := fun t : ℝ => f (t • y) - t ^ 2 * ‖y‖ ^ 2 / 2
  let g := fun t : ℝ => inner ℝ (G (t • y) - t • y) y
  have hd t (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt F (g t) t := by
    have hf := segment_hasDerivAt f (fun z => innerSL ℝ (G z)) 0 y t
      (by simpa using hF _ (hp t ht))
    have hq := (((hasDerivAt_id t).pow 2).mul_const (‖y‖ ^ 2)).div_const 2
    have hf' : HasDerivAt (fun t : ℝ => f (t • y)) (inner ℝ (G (t • y)) y) t := by
      simpa using hf
    have hq' : HasDerivAt (fun t : ℝ => t ^ 2 * ‖y‖ ^ 2 / 2)
        (t * ‖y‖ ^ 2) t := by
      convert hq using 1
      all_goals simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
      all_goals ring
    convert hf'.sub hq' using 1
    simp [g, inner_sub_left, inner_smul_left]
  have hg : ContinuousOn g (Icc (0 : ℝ) 1) := by
    have hc : ContinuousOn G S := fun z hz => (hG z hz).continuousAt.continuousWithinAt
    exact ((hc.comp (continuous_id.smul continuous_const).continuousOn hp).sub
      (continuous_id.smul continuous_const).continuousOn).inner continuousOn_const
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa using ht))
    (hg.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1))
  have hb : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖g t‖ ≤ t ^ 2 * ((L : ℝ) * ‖y‖ ^ 3 / 2) := by
    intro t ht
    have h := krylov.Nonlinear.gradient_model_quadratic_error G H
      (ContinuousLinearMap.id ℝ E) S hS h₀ hH₀ hH hG (t • y) (hp t ht)
    simp only [hG₀, sub_zero, ContinuousLinearMap.id_apply, norm_smul,
      Real.norm_of_nonneg ht.1] at h
    calc
      ‖g t‖ ≤ ‖G (t • y) - t • y‖ * ‖y‖ := norm_inner_le_norm _ _
      _ ≤ ((L : ℝ) / 2 * (t * ‖y‖) ^ 2) * ‖y‖ :=
        mul_le_mul_of_nonneg_right h (norm_nonneg _)
      _ = _ := by ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (by norm_num : (0 : ℝ) ≤ 1) (f := g)
    (g := fun t : ℝ => t ^ 2 * ((L : ℝ) * ‖y‖ ^ 3 / 2))
    (Filter.Eventually.of_forall fun t ht => hb t ⟨ht.1.le, ht.2⟩)
    (((continuous_pow 2).mul continuous_const).intervalIntegrable 0 1)
  rw [he] at hi
  have hi' : |f y - ‖y‖ ^ 2 / 2 - f 0| ≤ (L : ℝ) * ‖y‖ ^ 3 / 6 := by
    convert hi using 1 <;>
      simp [F, Real.norm_eq_abs, intervalIntegral.integral_mul_const, integral_pow]
    ring
  convert hi' using 1
  congr 1
  ring

end
end krylov.Functions
