import krylov.Design.SechGridLimit
import LeanCert.Tactic

/-!
Article: main_krylov, the numerical lower-majorant coefficient 0.66274 after thm:B.
Use: certify a compact rational enclosure for the genuine continuous maximum,
with the actual stationary point located by monotonicity, not supplied as data.
Source: the preceding exact calculus and LeanCert's proved interval enclosure
rules. All numerical certificate checking here uses the Lean kernel.
-/

namespace krylov.Design
noncomputable section
open Real Set jacobi.Young

set_option leancert.trust "kernel"

/-- Checked lower rational bracket for the actual stationary-point equation.
Article: main_krylov, the lower-majorant coefficient. -/
theorem mul_tanh_lower_bracket :
    (1199678 / 1000000 : ℝ) * tanh (1199678 / 1000000) < 1 := by
  have hc : 0 < (2199678 : ℝ) * exp (-(1199678 / 1000000)) -
      199678 * exp (1199678 / 1000000) := by
    leancert (taylorDepth := 30)
  rw [Real.tanh_eq, ← mul_div_assoc]
  apply (div_lt_one (add_pos (Real.exp_pos _) (Real.exp_pos _))).mpr
  linarith

/-- Checked upper rational bracket for the actual stationary-point equation.
Article: main_krylov, the lower-majorant coefficient. -/
theorem mul_tanh_upper_bracket :
    1 < (1199679 / 1000000 : ℝ) * tanh (1199679 / 1000000) := by
  have hc : 0 < (199679 : ℝ) * exp (1199679 / 1000000) -
      2199679 * exp (-(1199679 / 1000000)) := by
    leancert (taylorDepth := 30)
  rw [Real.tanh_eq, ← mul_div_assoc]
  apply (one_lt_div (add_pos (Real.exp_pos _) (Real.exp_pos _))).mpr
  linarith

/-- The genuinely constructed unique optimizer lies in an explicit rational interval.
Article: main_krylov, the lower-majorant optimizer. -/
theorem sechOptimizer_rational_bounds :
    (1199678 / 1000000 : ℝ) < sechOptimizer ∧ sechOptimizer < 1199679 / 1000000 := by
  have hr : 0 ≤ sechOptimizer := le_trans (by norm_num) sechOptimizer_spec.1.1.le
  constructor
  · by_contra hn
    have h := mul_tanh_strictMonoOn.monotoneOn hr (by norm_num : (0 : ℝ) ≤ 1199678 / 1000000)
      (le_of_not_gt hn)
    rw [sechOptimizer_spec.2] at h
    exact (not_le_of_gt mul_tanh_lower_bracket) h
  · by_contra hn
    have h := mul_tanh_strictMonoOn.monotoneOn (by norm_num : (0 : ℝ) ≤ 1199679 / 1000000) hr
      (le_of_not_gt hn)
    rw [sechOptimizer_spec.2] at h
    exact (not_le_of_gt mul_tanh_upper_bracket) h

/-- The actual maximum rounds to the source coefficient 0.66274.
Article: main_krylov, the asymptotic lower Chebyshev coefficient.
Proof: evaluate one actual test point for the lower bound; use the certified
optimizer bracket and monotonicity of sech for the upper bound. -/
theorem sechProfile_max_rational_bounds :
    (662743 / 1000000 : ℝ) < sechProfile sechOptimizer ∧
      sechProfile sechOptimizer < 662744 / 1000000 := by
  have hl : (662743 / 1000000 : ℝ) < (6 / 5 : ℝ) / cosh (6 / 5) := by
    apply (lt_div_iff₀ (Real.cosh_pos _)).mpr
    rw [Real.cosh_eq]
    simp only [div_eq_mul_inv]
    leancert (taylorDepth := 30)
  have hu : (1199679 / 1000000 : ℝ) / cosh (1199678 / 1000000) < 662744 / 1000000 := by
    apply (div_lt_iff₀ (Real.cosh_pos _)).mpr
    rw [Real.cosh_eq]
    simp only [div_eq_mul_inv]
    leancert (taylorDepth := 30)
  constructor
  · apply lt_of_lt_of_le _ (sechProfile_le_max (by norm_num : (0 : ℝ) ≤ 6 / 5))
    simpa only [sechProfile, sech, div_eq_mul_inv] using hl
  · apply lt_of_le_of_lt _ hu
    rw [sechProfile, div_eq_mul_inv]
    apply mul_le_mul sechOptimizer_rational_bounds.2.le _ (sech_pos _).le (by norm_num)
    exact sech_antitoneOn (by norm_num : (0 : ℝ) ≤ 1199678 / 1000000)
      (le_trans (by norm_num) sechOptimizer_spec.1.1.le) sechOptimizer_rational_bounds.1.le

end
end krylov.Design
