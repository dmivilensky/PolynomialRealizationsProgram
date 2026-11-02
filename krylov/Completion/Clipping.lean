import Mathlib.Tactic
set_option autoImplicit false
/-!
Article: main_krylov, thm:radau, clipping clause.
Use: clipping an arbitrary positive curvature estimate to its feasible interval
improves both the evaluated-step and virtual-correction relative errors.
Source: scalar order on a positive interval; both inequalities are proved here.
-/

namespace krylov.Completion
noncomputable section

/-- Clip a curvature estimate to the closed feasible curvature interval.
Use: the rule remains defined at a collapsed interval and at both endpoints.
Article: main_krylov, thm:radau.
Proof: first truncate at the upper endpoint and then at the lower endpoint. -/
def clipCurvature (a b x : ℝ) : ℝ := max a (min b x)

/-- Clipping produces a feasible positive curvature, including a singleton interval.
Use: the resulting reciprocal trial is well defined on every admissible input.
Article: main_krylov, thm:radau.
Proof: the maximum enforces the lower bound and both maximum arguments are
bounded above by the upper endpoint. -/
theorem clip_curvature_mem {a b : ℝ} (ha : 0<a) (hab : a≤b) (x : ℝ) :
    0<clipCurvature a b x ∧ clipCurvature a b x∈Set.Icc a b := by
  exact ⟨ha.trans_le (le_max_left _ _),le_max_left _ _,
    max_le hab (min_le_left _ _)⟩

/-- Clipping fixes every feasible curvature estimate.
Use: data-consistent estimates are preserved, including feasible endpoints.
Article: main_krylov, thm:radau.
Proof: both order truncations fix a point of the interval. -/
theorem clip_curvature_eq {a b x : ℝ} (hax : a≤x) (hxb : x≤b) :
    clipCurvature a b x=x := by
  simp only [clipCurvature,min_eq_right hxb,max_eq_right hax]

/-- Clipping improves the relative evaluated-step error for every feasible curvature.
Use: this is the article's curvature clipping inequality, with the unknown
true curvature in the numerator.
Article: main_krylov, thm:radau.
Proof: below the interval both relative errors are nonpositive and reciprocal
order improves them; above it both are nonnegative and reciprocal order again
improves them. Inside the interval the estimate is unchanged. -/
theorem clip_curvature_trial_error {a b c x : ℝ} (ha : 0<a)
    (hac : a≤c) (hcb : c≤b) (hx : 0<x) :
    |1-c/clipCurvature a b x|≤|1-c/x| := by
  have hc : 0<c := ha.trans_le hac
  have hb : 0<b := hc.trans_le hcb
  by_cases hxa : x<a
  · have he : clipCurvature a b x=a := by
      simp only [clipCurvature,min_eq_right (hxa.le.trans (hac.trans hcb)),max_eq_left hxa.le]
    rw [he,abs_of_nonpos (by have := (one_le_div₀ ha).mpr hac; linarith : 1-c/a≤0),
      abs_of_nonpos (by have := (one_le_div₀ hx).mpr (hxa.le.trans hac); linarith : 1-c/x≤0)]
    linarith [div_le_div_of_nonneg_left hc.le hx hxa.le]
  · have hax : a≤x := le_of_not_gt hxa
    by_cases hbx : b<x
    · have he : clipCurvature a b x=b := by
        simp only [clipCurvature,min_eq_left hbx.le,max_eq_right (hac.trans hcb)]
      rw [he,abs_of_nonneg (by have := (div_le_one₀ hb).mpr hcb; linarith : 0≤1-c/b),
        abs_of_nonneg (by have := (div_le_one₀ hx).mpr (hcb.trans hbx.le); linarith : 0≤1-c/x)]
      linarith [div_le_div_of_nonneg_left hc.le hb hbx.le]
    · rw [clip_curvature_eq hax (le_of_not_gt hbx)]

/-- Clipping also improves the reciprocal relative error used by virtual corrections.
Use: the same feasible clipping rule is valid for both one-gradient error conventions.
Article: main_krylov, thm:radau.
Proof: below and above the interval the signed errors have a common sign;
monotonicity of division by the positive true curvature gives the result. -/
theorem clip_curvature_virtual_error {a b c x : ℝ} (ha : 0<a)
    (hac : a≤c) (hcb : c≤b) :
    |1-clipCurvature a b x/c|≤|1-x/c| := by
  have hc : 0<c := ha.trans_le hac
  by_cases hxa : x<a
  · have he : clipCurvature a b x=a := by
      simp only [clipCurvature,min_eq_right (hxa.le.trans (hac.trans hcb)),max_eq_left hxa.le]
    rw [he,abs_of_nonneg (by have := (div_le_one₀ hc).mpr hac; linarith : 0≤1-a/c),
      abs_of_nonneg (by have := (div_le_one₀ hc).mpr (hxa.le.trans hac); linarith : 0≤1-x/c)]
    linarith [div_le_div_of_nonneg_right hxa.le hc.le]
  · have hax : a≤x := le_of_not_gt hxa
    by_cases hbx : b<x
    · have he : clipCurvature a b x=b := by
        simp only [clipCurvature,min_eq_left hbx.le,max_eq_right (hac.trans hcb)]
      rw [he,abs_of_nonpos (by have := (one_le_div₀ hc).mpr hcb; linarith : 1-b/c≤0),
        abs_of_nonpos (by have := (one_le_div₀ hc).mpr (hcb.trans hbx.le); linarith : 1-x/c≤0)]
      linarith [div_le_div_of_nonneg_right hbx.le hc.le]
    · rw [clip_curvature_eq hax (le_of_not_gt hbx)]

end
end krylov.Completion
