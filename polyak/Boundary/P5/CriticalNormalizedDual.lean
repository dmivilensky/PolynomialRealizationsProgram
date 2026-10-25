import polyak.Boundary.P5.CriticalDual
import polyak.Boundary.P5.NormalizedDual

/-!
Article: Proposition p5h0dual in the original normalized dual convention.
Use: the factor 15 in the exact source numerator is its positive common
denominator, so the resulting factorization is exactly the article's Q.
-/
noncomputable section
namespace polyak.Boundary.P5
open Spectral

/-- Article: the positive normalized dual simplex at the exact critical point. -/
def criticalWeights : DualWeights :=
  weights235 w2₀ w3₀ w2₀_bounds.1.le w3₀_bounds.1.le
    (by linarith [critical_weights_sum,w5₀_bounds.1])

/-- Article: the critical source polynomial is the same actual central dual numerator. -/
theorem dualReal_critical_closed : dualReal 0 criticalPoint=dualClosed (1/2) 1 w2₀ w3₀ := by
  rw [dualReal_closed]
  simp

/-- Article: Proposition p5h0dual, the actual normalized dual has the printed double-square factor. -/
theorem critical_normalized_dual_factor (c : ℝ) :
    (dualPolynomial criticalWeights (1/2) 1).eval c=
      (c+1/2)^2*(c-y₀)^2*(q2₀*c^2+q1₀*c+q0₀) := by
  rw [criticalWeights,dualPolynomial_eq_source_of_le (by norm_num : (1 : ℝ)≤1)]
  rw [← dualReal_critical_closed,critical_dual_factor]
  norm_num
  ring

/-- Article: whole-frequency nonnegativity of the actual normalized critical dual. -/
theorem critical_normalized_dual_nonneg (c : Frequency) :
    0≤(dualPolynomial criticalWeights (1/2) 1).eval (c : ℝ) := by
  rw [critical_normalized_dual_factor]
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (critical_dual_residual_pos c).le

/-- Article: the actual normalized dual has exactly the two critical contact frequencies. -/
theorem critical_normalized_dual_zero_iff (c : Frequency) :
    (dualPolynomial criticalWeights (1/2) 1).eval (c : ℝ)=0 ↔
      (c : ℝ)= -1/2 ∨ (c : ℝ)=y₀ := by
  have hsource := critical_dual_zero_iff c
  rw [critical_dual_factor] at hsource
  rw [critical_normalized_dual_factor]
  constructor
  · intro h
    apply hsource.mp
    linear_combination (15 : ℝ)*h
  · intro h
    have hz := hsource.mpr h
    linarith

end polyak.Boundary.P5
