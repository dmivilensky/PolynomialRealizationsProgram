import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
Article: main_krylov, apG:sc(i), the scalar self-concordant comparison.
Use: obtain the exact radial reciprocal-square-root estimate from the actual
self-concordance differential inequality. This is the scalar comparison step
in the canonical Hessian sandwich, with no Hessian bound assumed.
Source: Nesterov18, Theorem 5.1.7; the proof differentiates the reciprocal square
root and applies the real mean value theorem.
-/

namespace krylov.Functions
noncomputable section
open Set

/-- A nonnegative scalar self-concordant Hessian cannot acquire a zero from a
positive initial value.
Article: main_krylov, apG:sc(i), nondegeneracy propagation.
Proof: compactness bounds its square root, so an exponential integrating
factor has nonnegative derivative. Its positive initial value stays positive. -/
theorem selfConcordant_scalar_positive (p p' : ℝ → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hp₀ : 0 < p 0) (hp : ∀ t ∈ Icc (0 : ℝ) r, 0 ≤ p t)
    (hd : ∀ t ∈ Icc (0 : ℝ) r, HasDerivAt p (p' t) t)
    (hsc : ∀ t ∈ Icc (0 : ℝ) r, |p' t| ≤ 2 * (Real.sqrt (p t)) ^ 3) :
    ∀ t ∈ Icc (0 : ℝ) r, 0 < p t := by
  have hc : ContinuousOn p (Icc 0 r) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (Real.continuous_sqrt.comp_continuousOn hc)
  let C : ℝ := 2 * max B 0
  have hb t (ht : t ∈ Icc (0 : ℝ) r) : |p' t| ≤ C * p t := by
    have hs : Real.sqrt (p t) ≤ max B 0 := by
      have h := hB t ht
      change ‖Real.sqrt (p t)‖ ≤ B at h
      rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)] at h
      exact h.trans (le_max_left _ _)
    calc
      |p' t| ≤ 2 * (Real.sqrt (p t)) ^ 3 := hsc t ht
      _ = 2 * Real.sqrt (p t) * p t := by rw [pow_succ, Real.sq_sqrt (hp t ht)]; ring
      _ ≤ C * p t := by
        dsimp [C]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num)) (hp t ht)
  let u := fun t : ℝ => p t * Real.exp (C * t)
  let u' := fun t : ℝ => (p' t + C * p t) * Real.exp (C * t)
  have hu t (ht : t ∈ Icc (0 : ℝ) r) : HasDerivAt u (u' t) t := by
    convert! (hd t ht).mul (((hasDerivAt_id t).const_mul C).exp) using 1
    dsimp [u']
    ring
  have hb' t (ht : t ∈ Icc (0 : ℝ) r) : 0 ≤ u' t := by
    dsimp [u']
    apply mul_nonneg _ (Real.exp_pos _).le
    linarith [(abs_le.mp (hb t ht)).1]
  have hm : MonotoneOn u (Icc 0 r) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 r)
      (fun t ht => (hu t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hu t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => hb' t (interior_subset ht))
  intro t ht
  have h := hm (left_mem_Icc.mpr hr) ht ht.1
  simp only [u, mul_zero, Real.exp_zero, mul_one] at h
  exact (mul_pos_iff_of_pos_right (Real.exp_pos _)).mp (hp₀.trans_le h)

/-- The reciprocal square root of a positive self-concordant scalar Hessian
is one-Lipschitz on its actual interval.
Article: main_krylov, apG:sc(i), scalar comparison.
Proof: its actual derivative is bounded by one after cancelling the three
positive square-root factors in the self-concordance inequality. -/
theorem selfConcordant_reciprocal_sqrt_lipschitz (p p' : ℝ → ℝ) (r : ℝ)
    (hp : ∀ t ∈ Icc (0 : ℝ) r, 0 < p t)
    (hd : ∀ t ∈ Icc (0 : ℝ) r, HasDerivAt p (p' t) t)
    (hsc : ∀ t ∈ Icc (0 : ℝ) r, |p' t| ≤ 2 * (Real.sqrt (p t)) ^ 3) :
    LipschitzOnWith 1 (fun t : ℝ => (Real.sqrt (p t))⁻¹) (Icc 0 r) := by
  apply (convex_Icc (0 : ℝ) r).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
  · intro t ht
    exact (((hd t ht).sqrt (hp t ht).ne').inv (Real.sqrt_pos.mpr (hp t ht)).ne').hasDerivWithinAt
  · intro t ht
    have hs : 0 < Real.sqrt (p t) := Real.sqrt_pos.mpr (hp t ht)
    have he : -(p' t / (2 * Real.sqrt (p t))) / (Real.sqrt (p t)) ^ 2 =
        -(p' t) / (2 * (Real.sqrt (p t)) ^ 3) := by ring
    have hb : |-(p' t) / (2 * (Real.sqrt (p t)) ^ 3)| ≤ 1 := by
      rw [abs_div, abs_neg, abs_of_pos (by positivity : 0 < 2 * (Real.sqrt (p t)) ^ 3)]
      exact (div_le_one (by positivity)).mpr (hsc t ht)
    rw [he] 
    exact_mod_cast hb

/-- The radial self-concordant Hessian has the printed inverse-square upper bound.
Article: main_krylov, apG:sc(i), radial case.
Proof: compare the reciprocal square root with its true value one at zero,
then invert the positive lower bound at the endpoint. -/
theorem selfConcordant_scalar_upper (p p' : ℝ → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hr1 : r < 1) (hp₀ : p 0 = 1)
    (hp : ∀ t ∈ Icc (0 : ℝ) r, 0 < p t)
    (hd : ∀ t ∈ Icc (0 : ℝ) r, HasDerivAt p (p' t) t)
    (hsc : ∀ t ∈ Icc (0 : ℝ) r, |p' t| ≤ 2 * (Real.sqrt (p t)) ^ 3) :
    Real.sqrt (p r) ≤ (1 - r)⁻¹ ∧ p r ≤ (1 - r)⁻¹ ^ 2 := by
  have hl := selfConcordant_reciprocal_sqrt_lipschitz p p' r hp hd hsc
  have hb := hl.norm_sub_le (right_mem_Icc.mpr hr) (left_mem_Icc.mpr hr)
  simp only [hp₀, Real.sqrt_one, inv_one, sub_zero, Real.norm_eq_abs,
    abs_of_nonneg hr, NNReal.coe_one, one_mul] at hb
  have hq : 1 - r ≤ (Real.sqrt (p r))⁻¹ := by
    have := (abs_le.mp hb).1
    linarith
  have hs : 0 < Real.sqrt (p r) := Real.sqrt_pos.mpr (hp r (right_mem_Icc.mpr hr))
  have hupper : Real.sqrt (p r) ≤ (1 - r)⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ (sub_pos.mpr hr1)).mpr
    have hh := mul_le_mul_of_nonneg_right hq hs.le
    rw [inv_mul_cancel₀ hs.ne'] at hh
    nlinarith
  refine ⟨hupper, ?_⟩
  have hh := mul_self_le_mul_self (Real.sqrt_nonneg (p r)) hupper
  simpa only [← pow_two, Real.sq_sqrt (hp r (right_mem_Icc.mpr hr)).le] using hh

/-- The radial Hessian has the global inverse-square lower comparison.
Article: main_krylov, apG:sc(ii), the lower potential bound.
Proof: use the opposite side of the same reciprocal-square-root Lipschitz
estimate. Its denominator 1+r stays positive at every nonnegative radius. -/
theorem selfConcordant_scalar_lower (p p' : ℝ → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hp₀ : p 0 = 1) (hp : ∀ t ∈ Icc (0 : ℝ) r, 0 < p t)
    (hd : ∀ t ∈ Icc (0 : ℝ) r, HasDerivAt p (p' t) t)
    (hsc : ∀ t ∈ Icc (0 : ℝ) r, |p' t| ≤ 2 * (Real.sqrt (p t)) ^ 3) :
    (1 + r)⁻¹ ^ 2 ≤ p r := by
  have hl := selfConcordant_reciprocal_sqrt_lipschitz p p' r hp hd hsc
  have hb := hl.norm_sub_le (right_mem_Icc.mpr hr) (left_mem_Icc.mpr hr)
  simp only [hp₀, Real.sqrt_one, inv_one, sub_zero, Real.norm_eq_abs,
    abs_of_nonneg hr, NNReal.coe_one, one_mul] at hb
  have hq : (Real.sqrt (p r))⁻¹ ≤ 1 + r := by
    have := (abs_le.mp hb).2
    linarith
  have hs : 0 < Real.sqrt (p r) := Real.sqrt_pos.mpr (hp r (right_mem_Icc.mpr hr))
  have hlower : (1 + r)⁻¹ ≤ Real.sqrt (p r) := by
    rw [← one_div]
    apply (div_le_iff₀ (by positivity : 0 < 1 + r)).mpr
    have hh := mul_le_mul_of_nonneg_right hq hs.le
    rw [inv_mul_cancel₀ hs.ne'] at hh
    nlinarith
  have hh := mul_self_le_mul_self (by positivity : 0 ≤ (1 + r)⁻¹) hlower
  simpa only [← pow_two, Real.sq_sqrt (hp r (right_mem_Icc.mpr hr)).le] using hh

/-- The exact mixed scalar differential bound propagates the canonical Hessian sandwich.
Article: main_krylov, apG:sc(i).
Proof: differentiate the two integrating factors a(t)(1-t)^2 and
a(t)/(1-t)^2. Their opposite monotonicities give the two printed endpoint
factors. This is a differential comparison, not an assumed metric estimate. -/
theorem selfConcordant_mixed_scalar_sandwich (a a' : ℝ → ℝ) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1)
    (hd : ∀ t ∈ Icc (0 : ℝ) r, HasDerivAt a (a' t) t)
    (hb : ∀ t ∈ Icc (0 : ℝ) r, |a' t| ≤ 2 * a t / (1 - t)) :
    (1 - r) ^ 2 * a 0 ≤ a r ∧ a r ≤ (1 - r)⁻¹ ^ 2 * a 0 := by
  let u := fun t : ℝ => a t * (1 - t) ^ 2
  let v := fun t : ℝ => a t / (1 - t) ^ 2
  let u' := fun t : ℝ => a' t * (1 - t) ^ 2 - 2 * a t * (1 - t)
  let v' := fun t : ℝ => (a' t * (1 - t) ^ 2 + 2 * a t * (1 - t)) / (1 - t) ^ 4
  have hpos t (ht : t ∈ Icc (0 : ℝ) r) : 0 < 1 - t := by linarith [ht.2]
  have hu t (ht : t ∈ Icc (0 : ℝ) r) : HasDerivAt u (u' t) t := by
    convert! (hd t ht).mul (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).pow 2) using 1
    dsimp [u']
    ring
  have hv t (ht : t ∈ Icc (0 : ℝ) r) : HasDerivAt v (v' t) t := by
    convert! (hd t ht).div (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).pow 2)
      (pow_ne_zero 2 (hpos t ht).ne') using 1
    dsimp [v']
    ring
  have hub t (ht : t ∈ Icc (0 : ℝ) r) : u' t ≤ 0 := by
    have hp := hpos t ht
    have h := (le_div_iff₀ hp).mp (abs_le.mp (hb t ht)).2
    have hh := mul_le_mul_of_nonneg_right h hp.le
    dsimp [u']
    nlinarith
  have hvb t (ht : t ∈ Icc (0 : ℝ) r) : 0 ≤ v' t := by
    have hp := hpos t ht
    have h := (div_le_iff₀ hp).mp (by simpa only [neg_div] using (abs_le.mp (hb t ht)).1 :
      -(2 * a t) / (1 - t) ≤ a' t)
    have hh := mul_le_mul_of_nonneg_right h hp.le
    dsimp [v']
    apply div_nonneg _ (by positivity)
    nlinarith
  have huanti : AntitoneOn u (Icc 0 r) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 r)
      (fun t ht => (hu t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hu t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => hub t (interior_subset ht))
  have hvmono : MonotoneOn v (Icc 0 r) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 r)
      (fun t ht => (hv t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hv t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => hvb t (interior_subset ht))
  have hlo := hvmono (left_mem_Icc.mpr hr) (right_mem_Icc.mpr hr) hr
  have hhi := huanti (left_mem_Icc.mpr hr) (right_mem_Icc.mpr hr) hr
  simp only [u, v, sub_zero, one_pow, mul_one, div_one] at hlo hhi
  constructor
  · have h := (le_div_iff₀ (sq_pos_of_pos (sub_pos.mpr hr1))).mp hlo
    nlinarith
  · have h := (le_div_iff₀ (sq_pos_of_pos (sub_pos.mpr hr1))).mpr hhi
    simpa only [inv_pow, div_eq_inv_mul] using h

end
end krylov.Functions
