import krylov.XR.Backtracking
import Mathlib.Analysis.Convex.Segment

/-!
Article: main_krylov, thm:grow, genuinely local Armijo termination.
Use: derive the local backtracking threshold near the accepted limit using
only derivatives and Lipschitz gradient on a neighbourhood. No global
Lipschitz assumption is added to G1. Source: integrate the true derivative
on a segment contained in the local ball; then use the actual clipped
backtracking factors [2,10].
-/

namespace krylov.XR
noncomputable section
open Set MeasureTheory Metric
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The sharp descent lemma uses only the genuine function/gradient on a
convex local ball containing the tested segment. -/
theorem descent_lemma_on_ball (f : E → ℝ) (G : E → E) (center : E) (radius : ℝ)
    (hF : ∀ z ∈ ball center radius, HasFDerivAt f (innerSL ℝ (G z)) z)
    (L : ℝ≥0) (hG : LipschitzOnWith L G (ball center radius))
    (x s : E) (hx : x ∈ ball center radius) (hxs : x + s ∈ ball center radius) :
    |f (x + s) - f x - inner ℝ (G x) s| ≤ (L : ℝ) * ‖s‖ ^ 2 / 2 := by
  let F := fun t : ℝ => f (x + t • s) - t * inner ℝ (G x) s
  let d := fun t : ℝ => inner ℝ (G (x + t • s) - G x) s
  have hseg t (ht : t ∈ Icc (0 : ℝ) 1) : x + t • s ∈ ball center radius := by
    have h := (convex_ball center radius).segment_subset hx hxs
      (lineMap_mem_segment ℝ x (x + s) ht)
    have he : AffineMap.lineMap x (x + s) t = x + t • s := by
      rw [AffineMap.lineMap_apply_module]
      module
    rwa [he] at h
  have hd t (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt F (d t) t := by
    have hf := krylov.Functions.segment_hasDerivAt f
      (fun z => innerSL ℝ (G z)) x s t (hF _ (hseg t ht))
    convert hf.sub ((hasDerivAt_id t).mul_const (inner ℝ (G x) s)) using 1
    · rfl
    · simp [d, inner_sub_left]
  have hc : ContinuousOn d (Icc (0 : ℝ) 1) :=
    ((hG.continuousOn.comp
      (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hseg).sub
      continuousOn_const).inner continuousOn_const
  have hic : ContinuousOn d (uIcc (0 : ℝ) 1) := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hc
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht))
    hic.intervalIntegrable
  have hb t (ht : t ∈ Icc (0 : ℝ) 1) : ‖d t‖ ≤ t * ((L : ℝ) * ‖s‖ ^ 2) := by
    have hg := hG.norm_sub_le (hseg t ht) hx
    simp only [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1] at hg
    calc
      ‖d t‖ ≤ ‖G (x + t • s) - G x‖ * ‖s‖ := norm_inner_le_norm _ _
      _ ≤ ((L : ℝ) * (t * ‖s‖)) * ‖s‖ := mul_le_mul_of_nonneg_right hg (norm_nonneg _)
      _ = _ := by ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (by norm_num : (0 : ℝ) ≤ 1) (f := d) (g := fun t : ℝ => t * ((L : ℝ) * ‖s‖ ^ 2))
    (Filter.Eventually.of_forall fun t ht => hb t ⟨ht.1.le, ht.2⟩)
    ((continuous_id.mul continuous_const).intervalIntegrable 0 1)
  rw [he] at hi
  have hid : F 1 - F 0 = f (x + s) - f x - inner ℝ (G x) s := by
    dsimp only [F]
    simp only [one_smul, zero_smul, add_zero, zero_mul, sub_zero, one_mul]
    ring
  rw [hid, Real.norm_eq_abs] at hi
  norm_num [intervalIntegral.integral_mul_const] at hi
  convert hi using 1
  ring

/-- A positive sufficient-acceptance threshold forces termination of the
literal quotient recursion; it is not an input to the executor. -/
theorem backtracking_threshold (f : E → ℝ) (sigma : ℝ) (x g u : E)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (hsmall : ∀ t, 0 < t → t ≤ threshold → Accepted f sigma x g u t) :
    (∃ j, Accepted f sigma x g u (backtrackingSteps f x g u j)) ∧
      min 1 (threshold / 10) ≤ backtrackingLength f sigma x g u := by
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hthreshold (by norm_num : (1 / 2 : ℝ) < 1)
  have hex : ∃ j, Accepted f sigma x g u (backtrackingSteps f x g u j) :=
    ⟨j, hsmall _ (backtrackingSteps_bounds _ _ _ _ j).1
      ((backtrackingSteps_bounds _ _ _ _ j).2.trans hj.le)⟩
  refine ⟨hex, ?_⟩
  have hs := (backtrackingIndex_spec f sigma x g u hex).2
  generalize hn : backtrackingIndex f sigma x g u = N
  cases N with
  | zero => simp [backtrackingLength, hn, backtrackingSteps]
  | succ j =>
    have hreject := hs j (by omega)
    have hb := backtrackingSteps_bounds f x g u j
    have ht : threshold < backtrackingSteps f x g u j := by
      by_contra h
      exact hreject (hsmall _ hb.1 (le_of_not_gt h))
    have hc := reductionFactor_bounds (trialQuotient f x g u (backtrackingSteps f x g u j))
    have hfac : 0 < reductionFactor (trialQuotient f x g u (backtrackingSteps f x g u j)) := by linarith
    have hnxt : backtrackingSteps f x g u j / 10 ≤ backtrackingLength f sigma x g u := by
      rw [backtrackingLength, hn, backtrackingSteps]
      exact div_le_div_of_nonneg_left hb.1.le hfac hc.2
    exact (min_le_right _ _).trans ((div_le_div_of_nonneg_right ht.le (by norm_num)).trans hnxt)

end
end krylov.XR
