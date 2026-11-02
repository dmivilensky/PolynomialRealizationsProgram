import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Tactic

/-!
Article: main_krylov, apB:lem:UAsteps, the small-step normalization mechanism.
Use: preserve uniform weighted direction estimates when individual reference
step lengths approach zero. These estimates are independent of a minimum step.
Source: reverse triangle inequality and exact norms of Hilbert rank-one operators.
-/

namespace krylov.Stability
noncomputable section
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Normalizing an actual nonzero vector costs at most twice its relative reference-step error.
Use: the reference length is retained as a weight rather than replaced by an inverse minimum length.
Article: main_krylov, apB:lem:UAsteps, ‖τ−q‖≤2‖σ−aq‖/a.
Proof: insert the actual vector between aτ and aq; reverse triangle bounds
the radial error by the same actual step error, and the two costs add. -/
theorem normalization_weighted (x q : E) (hx : x≠0) (hq : ‖q‖=1) (a : ℝ) (ha : 0<a) :
    a*‖NormedSpace.normalize x-q‖≤2*‖x-a • q‖ := by
  -- The radial and angular errors are both bounded before dividing by any small reference length.
  let t := NormedSpace.normalize x
  have ht : ‖t‖=1 := NormedSpace.norm_normalize hx
  have hx' : x=‖x‖ • t := (NormedSpace.norm_smul_normalize x).symm
  have hrad : ‖a • t-x‖≤‖x-a • q‖ := by
    have hn := abs_norm_sub_norm_le x (a • q)
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos ha, hq, mul_one] at hn
    calc
      ‖a • t-x‖ = ‖(a-‖x‖) • t‖ := by
        congr 1
        rw [sub_smul]
        exact congrArg (fun v => a • t-v) hx'
      _ = |‖x‖-a| := by rw [norm_smul, Real.norm_eq_abs, ht, mul_one, abs_sub_comm]
      _ ≤ _ := hn
  have htri : ‖a • t-a • q‖≤‖a • t-x‖+‖x-a • q‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (a • t-x) (x-a • q)
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos ha] at htri
  exact htri.trans (by linarith)

/-- The normalized angular error is bounded both absolutely and by its actual relative step error.
Use: explicitly covers large normalized changes when the reference step is tiny.
Article: main_krylov, apB:lem:UAsteps, min(2,2ε/a).
Proof: two actual unit vectors have distance at most two; the second bound is the weighted estimate divided by positive a. -/
theorem normalization_min_bound (x q : E) (hx : x≠0) (hq : ‖q‖=1) (a : ℝ) (ha : 0<a) :
    ‖NormedSpace.normalize x-q‖≤min 2 (2*‖x-a • q‖/a) := by
  apply le_min
  · simpa only [NormedSpace.norm_normalize hx, hq, one_add_one_eq_two] using norm_sub_le (NormedSpace.normalize x) q
  · exact (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using normalization_weighted x q hx hq a ha)

/-- Later-error weighting cancels the inverse reference-step length in the normalized direction bound.
Use: uniform projector estimates depend on a nonstagnation ratio rather than a smallest reference energy.
Article: main_krylov, apB:lem:UAsteps, weighted flag comparison.
Proof: multiply the angular error by r≤κa and use the actual weighted step-error estimate. -/
theorem normalization_error_weight (x q : E) (hx : x≠0) (hq : ‖q‖=1)
    (a r κ ε : ℝ) (ha : 0<a) (hκ : 0≤κ) (he : ‖x-a • q‖≤ε) (hr : r≤κ*a) :
    r*‖NormedSpace.normalize x-q‖≤2*κ*ε := by
  calc
    _ ≤ (κ*a)*‖NormedSpace.normalize x-q‖ := mul_le_mul_of_nonneg_right hr (norm_nonneg _)
    _ = κ*(a*‖NormedSpace.normalize x-q‖) := by ring
    _ ≤ κ*(2*‖x-a • q‖) := mul_le_mul_of_nonneg_left (normalization_weighted x q hx hq a ha) hκ
    _ ≤ 2*κ*ε := by nlinarith [mul_le_mul_of_nonneg_left he (mul_nonneg (by norm_num : (0 : ℝ)≤2) hκ)]

/-- Actual unit rank-one orthogonal projectors change by at most twice their unit-direction distance.
Use: convert weighted angular estimates to weighted actual flag-operator estimates.
Article: main_krylov, apB:lem:UAsteps, the sum of ττᵀ−qqᵀ terms.
Source: exact Hilbert rank-one operator norms.
Proof: split the difference into two true rank-one terms and apply their exact product norms. -/
theorem unit_rankOne_difference (u v : E) (hu : ‖u‖=1) (hv : ‖v‖=1) :
    ‖InnerProductSpace.rankOne ℝ u u-InnerProductSpace.rankOne ℝ v v‖≤2*‖u-v‖ := by
  -- Each changed factor is isolated in one genuine rank-one operator.
  have he : InnerProductSpace.rankOne ℝ u u-InnerProductSpace.rankOne ℝ v v=
      InnerProductSpace.rankOne ℝ (u-v) u+InnerProductSpace.rankOne ℝ v (u-v) := by
    ext x
    simp only [_root_.sub_apply, _root_.add_apply,
      InnerProductSpace.rankOne_apply, inner_sub_left]
    module
  rw [he]
  simpa only [InnerProductSpace.norm_rankOne, hu, hv, mul_one, one_mul, two_mul] using norm_add_le
    (InnerProductSpace.rankOne ℝ (u-v) u) (InnerProductSpace.rankOne ℝ v (u-v))

end
end krylov.Stability
