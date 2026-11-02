import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
Article: jacobi, Appendix C.3 (support weights and segment bounds).
The positive square-root weight exactly cancels the edge-frequency
power of the support envelope. These scalar inequalities retain the
original positive mesh scale and also apply to the derivative estimate.
Source: monotonicity of positive real powers and square roots.
Use: weighted_power_decay cancels the support-polynomial edge growth against the same original spectral probability.
-/
namespace jacobi.Support
noncomputable section
open Real

/-- The actual weight power bound passes to its positive square-root normalization with the exact half exponent.
Use: weighted_power_decay cancels the support-polynomial edge growth against the same original spectral probability.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: square both nonnegative expressions and use the exact original real-power exponent identity. -/
theorem sqrt_weight_power {N w C r g:ℝ} (hN:0≤N) (hw:0≤w) (hC:0<C) (hr:0<r)
    (h:N*w≤C*r^(2*g)) : sqrt (N*w)≤sqrt C*r^g := by
  have hp : (r^g)^2=r^(2*g) := by
    rw [pow_two,← rpow_add hr]
    congr 1
    ring
  apply (sq_le_sq₀ (sqrt_nonneg _) (mul_nonneg (sqrt_nonneg _) (rpow_pos_of_pos hr _).le)).mp
  rw [sq_sqrt (mul_nonneg hN hw),mul_pow,sq_sqrt hC.le,hp]
  exact h

/-- A genuine lower angular scale cancels the entire polynomial-growth weight in the spectral envelope.
Use: supportPolynomial_segment_bounds proves the original uniform weighted function and derivative estimates on every actual interpolation point.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: the negative power decreases on the positive axis, so theta^(-gamma) is at most (c*r)^(-gamma). The two exact r powers cancel. Multiply by the preceding positive square-root weight estimate. -/
theorem weighted_power_decay {N w C r g theta c:ℝ} (hN:0≤N) (hw:0≤w) (hC:0<C)
    (hr:0<r) (hg:0≤g) (hc:0<c) (htheta:c*r≤theta) (h:N*w≤C*r^(2*g)) :
    sqrt (N*w)*theta^(-g)≤sqrt C*c^(-g) := by
  -- The cancellation uses the original real exponents and requires no integer-exponent reduction.
  have ht : 0<theta := lt_of_lt_of_le (mul_pos hc hr) htheta
  have hp : r^g*theta^(-g)≤c^(-g) := by
    calc
      _ ≤ r^g*(c*r)^(-g) := mul_le_mul_of_nonneg_left
        (rpow_le_rpow_of_nonpos (mul_pos hc hr) htheta (neg_nonpos.mpr hg)) (rpow_pos_of_pos hr g).le
      _ = c^(-g)*(r^g*r^(-g)) := by rw [mul_rpow hc.le hr.le]; ring
      _ = _ := by rw [← rpow_add hr,add_neg_cancel,rpow_zero,mul_one]
  calc
    _ ≤ (sqrt C*r^g)*theta^(-g) := mul_le_mul_of_nonneg_right
      (sqrt_weight_power hN hw hC hr h) (rpow_pos_of_pos ht (-g)).le
    _ = sqrt C*(r^g*theta^(-g)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (sqrt_nonneg _)

end
end jacobi.Support
