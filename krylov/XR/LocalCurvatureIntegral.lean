import krylov.Functions.SegmentTrapezoid
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
Article: main_krylov, lem:mm and apG:local(c), genuine trial curvature.
Use: derive the weighted-Hessian curvature in the actual XR quotient from
the scalar objective's real first and second derivatives.
Source: the fundamental theorem of calculus applied to
f(x+t u)+(1-t) grad f(x+t u)·u (Taylor's integral formula).
-/

namespace krylov.XR
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exact normalization of the second-order Taylor weight. -/
theorem integral_taylor_weight : (∫ t in (0 : ℝ)..1, 1 - t) = 1 / 2 := by
  rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ)) (g := fun t : ℝ => t)
    intervalIntegrable_const (continuous_id.intervalIntegrable 0 1)]
  norm_num

/-- The actual scalar weighted-Hessian curvature of a real trial. -/
def weightedCurvature (H : E → E →L[ℝ] E) (x u : E) : ℝ :=
  2 * ∫ t in (0 : ℝ)..1, (1 - t) * inner ℝ (H (x + t • u) u) u

/-- Taylor's integral formula on the genuine trial segment. -/
theorem weightedCurvature_eq_values (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) (x u : E)
    (hF : ∀ t ∈ Icc (0 : ℝ) 1,
      HasFDerivAt f (innerSL ℝ (G (x + t • u))) (x + t • u))
    (hG : ∀ t ∈ Icc (0 : ℝ) 1, HasFDerivAt G (H (x + t • u)) (x + t • u))
    (hH : ContinuousOn (fun t : ℝ => H (x + t • u)) (Icc 0 1)) :
    weightedCurvature H x u = 2 * (f (x + u) - f x - inner ℝ (G x) u) := by
  let P := fun t : ℝ => f (x + t • u) + (1 - t) * inner ℝ (G (x + t • u)) u
  have hd t (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt P ((1 - t) * inner ℝ (H (x + t • u) u) u) t := by
    have hf := krylov.Functions.segment_hasDerivAt f (fun z => innerSL ℝ (G z))
      x u t (hF t ht)
    have hg := (krylov.Functions.segment_hasDerivAt G H x u t (hG t ht)).inner ℝ
      (hasDerivAt_const t u)
    have hw := (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
    convert hf.add (hw.mul hg) using 1
    · rfl
    · simp only [innerSL_apply_apply, inner_zero_right, zero_add, zero_sub, Pi.sub_apply, id_eq]
      ring
  have hc : ContinuousOn (fun t : ℝ => (1 - t) * inner ℝ (H (x + t • u) u) u) (Icc 0 1) :=
    (continuousOn_const.sub continuousOn_id).mul
      ((hH.clm_apply continuousOn_const).inner continuousOn_const)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa using ht))
    (hc.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1))
  have hp : P 1 - P 0 = f (x + u) - f x - inner ℝ (G x) u := by
    dsimp only [P]
    simp only [one_smul, zero_smul, add_zero]
    ring
  rw [weightedCurvature, he, hp]

/-- A primitive uniform Hessian allowance on the actual trial segment
gives the exact same allowance on its weighted curvature. -/
theorem weightedCurvature_error (H : E → E →L[ℝ] E) (Hstar : E →L[ℝ] E)
    (x u : E) (epsilon : ℝ) (_he : 0 ≤ epsilon)
    (hH : ContinuousOn (fun t : ℝ => H (x + t • u)) (Icc 0 1))
    (herror : ∀ t ∈ Icc (0 : ℝ) 1, ‖H (x + t • u) - Hstar‖ ≤ epsilon) :
    |weightedCurvature H x u - inner ℝ (Hstar u) u| ≤ epsilon * ‖u‖ ^ 2 := by
  let F := fun t : ℝ => (1 - t) * inner ℝ ((H (x + t • u) - Hstar) u) u
  have hc : ContinuousOn F (Icc (0 : ℝ) 1) :=
    (continuousOn_const.sub continuousOn_id).mul
      (((hH.sub continuousOn_const).clm_apply continuousOn_const).inner continuousOn_const)
  have hb t (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖F t‖ ≤ (1 - t) * (epsilon * ‖u‖ ^ 2) := by
    have hi := abs_real_inner_le_norm ((H (x + t • u) - Hstar) u) u
    have ho := ((H (x + t • u) - Hstar).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right (herror t ht) (norm_nonneg _))
    have hh : |inner ℝ ((H (x + t • u) - Hstar) u) u| ≤ epsilon * ‖u‖ ^ 2 :=
      hi.trans ((mul_le_mul_of_nonneg_right ho (norm_nonneg _)).trans_eq (by ring))
    dsimp only [F]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sub_nonneg.mpr ht.2)]
    exact mul_le_mul_of_nonneg_left hh (sub_nonneg.mpr ht.2)
  have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (by norm_num : (0 : ℝ) ≤ 1) (f := F)
    (g := fun t : ℝ => (1 - t) * (epsilon * ‖u‖ ^ 2))
    (Filter.Eventually.of_forall fun t ht => hb t ⟨ht.1.le, ht.2⟩)
    (((continuous_const.sub continuous_id).mul continuous_const).intervalIntegrable 0 1)
  have heq : 2 * (∫ t in (0 : ℝ)..1, F t) =
      weightedCurvature H x u - inner ℝ (Hstar u) u := by
    have h₁ : IntervalIntegrable (fun t : ℝ => (1 - t) * inner ℝ (H (x + t • u) u) u)
        volume 0 1 := ((continuousOn_const.sub continuousOn_id).mul
          ((hH.clm_apply continuousOn_const).inner continuousOn_const)).intervalIntegrable_of_Icc (by norm_num)
    have h₂ : IntervalIntegrable (fun t : ℝ => (1 - t) * inner ℝ (Hstar u) u) volume 0 1 :=
      ((continuous_const.sub continuous_id).mul continuous_const).intervalIntegrable 0 1
    simp only [F, _root_.sub_apply, inner_sub_left, mul_sub]
    rw [intervalIntegral.integral_sub h₁ h₂]
    norm_num [weightedCurvature, intervalIntegral.integral_mul_const, integral_taylor_weight]
    ring
  rw [← heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [Real.norm_eq_abs] at hi
  norm_num [intervalIntegral.integral_mul_const, integral_taylor_weight] at hi
  nlinarith

end
end krylov.XR
