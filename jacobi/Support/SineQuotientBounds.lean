import jacobi.Support.SineShiftBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
Article: jacobi, Appendix C.3 (top-node polynomials).
The genuine ratios of shifted support sines have uniform positive
bounds and a quantitative O(1/m) difference from one. These facts
are proved directly on the original growing index ranges and feed
both actual coupling positivity and the top-node difference estimate.
Use: coupling_lower and diagonal_zero_bound control the genuine support coefficients, including the actual small-index rows.
-/
namespace jacobi.Support
noncomputable section
open Real Filter
open scoped Topology

/-- The actual quotient of two positively shifted support lattice sines has uniform positive two-sided bounds throughout every original growing half-chain range.
Use: coupling_lower and diagonal_zero_bound control the genuine support coefficients, including the actual small-index rows.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: both original shifted sines are comparable with the same positive m*h; their common factor cancels exactly. -/
theorem sine_quotient_bounds (a b : ℝ) {p q : ℝ} (hp:-1<p) (hq:-1<q) (d : ℕ) :
    ∃c C:ℝ,0<c ∧ 0<C ∧ ∀ᶠn:ℕ in atTop,∀m:ℕ,0<m→2*m≤n+d→
      c≤sin (((m:ℝ)+p)*step a b n)/sin (((m:ℝ)+q)*step a b n) ∧
      sin (((m:ℝ)+p)*step a b n)/sin (((m:ℝ)+q)*step a b n)≤C := by
  -- The original m*h factor is genuinely positive on every used row.
  obtain ⟨c₁,C₁,hc₁,hC₁,h₁⟩ := shifted_sine_bounds a b hp d
  obtain ⟨c₂,C₂,hc₂,hC₂,h₂⟩ := shifted_sine_bounds a b hq d
  refine ⟨c₁/C₂,C₁/c₂,div_pos hc₁ hC₂,div_pos hC₁ hc₂,?_⟩
  filter_upwards [h₁,h₂] with n hn₁ hn₂
  intro m hm hmn
  have hm0 : (0:ℝ)<m := by exact_mod_cast hm
  have hscale : 0<(m:ℝ)*step a b n := mul_pos hm0 hn₁.1
  obtain ⟨hp₁,hp₂⟩ := hn₁.2 m hm hmn
  obtain ⟨hq₁,hq₂⟩ := hn₂.2 m hm hmn
  have hsin : 0<sin (((m:ℝ)+q)*step a b n) :=
    lt_of_lt_of_le (by nlinarith [mul_pos hc₂ hscale]) hq₁
  constructor
  · apply (le_div_iff₀ hsin).mpr
    have hmul := mul_le_mul_of_nonneg_left hq₂ (div_pos hc₁ hC₂).le
    have he : c₁/C₂*(C₂*(m:ℝ)*step a b n)=c₁*(m:ℝ)*step a b n := by field_simp
    exact hmul.trans (by rw [he]; exact hp₁)
  · apply (div_le_iff₀ hsin).mpr
    have hmul := mul_le_mul_of_nonneg_left hq₁ (div_pos hC₁ hc₂).le
    have he : C₁/c₂*(c₂*(m:ℝ)*step a b n)=C₁*(m:ℝ)*step a b n := by field_simp
    exact hp₂.trans (by rw [he] at hmul; exact hmul)

/-- Every actual shifted support sine quotient differs from one by at most a genuine uniform constant divided by its original positive index.
Use: the actual top-node squared-ratio estimate yields the printed first-difference bound for the original support polynomial.
Article: jacobi, Appendix C.3 (top-node polynomials).
Source: the global elementary sine Lipschitz bound, Real.abs_sin_sub_sin_le.
Proof: the original numerator difference is at most |p-q|*h; the actual denominator is at least c*m*h, with both factors positive. Cancel the same original lattice step. -/
theorem sine_quotient_error (a b : ℝ) {p q : ℝ} (hq:-1<q) (d : ℕ) :
    ∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,∀m:ℕ,0<m→2*m≤n+d→
      |sin (((m:ℝ)+p)*step a b n)/sin (((m:ℝ)+q)*step a b n)-1|≤C/(m:ℝ) := by
  -- No sign condition on the numerator shift is needed for this original difference estimate.
  obtain ⟨c₀,C₀,hc₀,hC₀,hbound⟩ := shifted_sine_bounds a b hq d
  refine ⟨1+|p-q|/c₀,by positivity,?_⟩
  filter_upwards [hbound] with n hn
  intro m hm hmn
  have hm0 : (0:ℝ)<m := by exact_mod_cast hm
  have hlo := (hn.2 m hm hmn).1
  have hscale : 0<(m:ℝ)*step a b n := mul_pos hm0 hn.1
  have hsin : 0<sin (((m:ℝ)+q)*step a b n) :=
    lt_of_lt_of_le (by nlinarith [mul_pos hc₀ hscale]) hlo
  have hdiff := Real.abs_sin_sub_sin_le (((m:ℝ)+p)*step a b n) (((m:ℝ)+q)*step a b n)
  rw [show ((m:ℝ)+p)*step a b n-((m:ℝ)+q)*step a b n=(p-q)*step a b n by ring,
    abs_mul,abs_of_pos hn.1] at hdiff
  rw [div_sub_one hsin.ne',abs_div,abs_of_pos hsin]
  calc
    _ ≤ (|p-q| *step a b n)/(c₀*(m:ℝ)*step a b n) :=
      div_le_div₀ (mul_nonneg (abs_nonneg _) hn.1.le) hdiff (by nlinarith [mul_pos hc₀ hscale]) hlo
    _ = (|p-q|/c₀)/(m:ℝ) := by field_simp [hc₀.ne',hm0.ne',hn.1.ne']
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hm0.le

end
end jacobi.Support
