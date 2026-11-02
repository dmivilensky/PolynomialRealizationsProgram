import jacobi.Finite.OscillatoryState

/-!
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
The original Jacobi recurrence is compared directly with its free
coefficient one half. All divisions use its actual positive coupling.
Use: Support.naturalWave_free_error discharges the original oscillatory-envelope error estimate using the actual proved support coefficients.
-/
namespace jacobi.Finite
noncomputable section
open Real

/-- The original positive Jacobi recurrence has the explicit free-wave error bound determined by its actual coefficient errors.
Use: Support.naturalWave_free_error discharges the original oscillatory-envelope error estimate using the actual proved support coefficients.
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
Proof: multiply the free error by the same original positive coupling. The exact original recurrence leaves two coefficient differences. Apply their genuine real error bounds and the finite complex triangle inequality, then divide by the positive coupling lower bound. -/
theorem free_recurrence_error_bound {a₁ a₂ b c H Y:ℝ} {x v w y:ℂ}
    (hc:0<c) (ha:c≤a₂) (hH:0≤H) (hY:0≤Y) (hy:‖y‖≤Y)
    (h₁:|a₁-1/2|≤H) (h₂:|a₂-1/2|≤H) (hb:|b|≤H)
    (hrec:(a₂:ℂ)*w+(a₁:ℂ)*x+(b:ℂ)*v=y*v) :
    ‖w-2*y*v+x‖≤((2*Y+2)/c)*H*(‖x‖+‖v‖) := by
  -- Multiplying by the original coupling preserves the exact recurrence before any complex norm comparison.
  have ha₂ : 0<a₂ := hc.trans_le ha
  have hreal : |1-2*a₂|≤2*H := by
    have hid : 1-2*a₂=(-2)*(a₂-1/2) := by ring
    rw [hid,abs_mul,abs_of_neg (by norm_num : (-2:ℝ)<0)]
    linarith
  have hdiff : |a₂-a₁|≤2*H := by
    have h := abs_sub (a₂-1/2) (a₁-1/2)
    rw [sub_sub_sub_cancel_right] at h
    linarith
  have heq : (a₂:ℂ)*(w-2*y*v+x)=(((1-2*a₂:ℝ):ℂ)*y-(b:ℂ))*v+((a₂-a₁:ℝ):ℂ)*x := by
    push_cast
    linear_combination hrec
  have hfirst : ‖((1-2*a₂:ℝ):ℂ)*y-(b:ℂ)‖≤2*H*Y+H := by
    calc
      _ ≤ ‖((1-2*a₂:ℝ):ℂ)*y‖+‖(b:ℂ)‖ := norm_sub_le _ _
      _ = |1-2*a₂| * ‖y‖+|b| := by rw [norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs]
      _ ≤ _ := add_le_add (mul_le_mul hreal hy (norm_nonneg _) (by positivity)) hb
  have hnorm : a₂*‖w-2*y*v+x‖≤(2*Y+2)*H*(‖x‖+‖v‖) := by
    calc
      _ = ‖(a₂:ℂ)*(w-2*y*v+x)‖ := by rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha₂]
      _ ≤ ‖(((1-2*a₂:ℝ):ℂ)*y-(b:ℂ))*v‖+‖((a₂-a₁:ℝ):ℂ)*x‖ := by rw [heq]; exact norm_add_le _ _
      _ ≤ (2*H*Y+H)*‖v‖+(2*H)*‖x‖ := by
        rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]
        exact add_le_add (mul_le_mul_of_nonneg_right hfirst (norm_nonneg _))
          (mul_le_mul_of_nonneg_right hdiff (norm_nonneg _))
      _ ≤ _ := by nlinarith only [mul_nonneg hH (norm_nonneg v),mul_nonneg (mul_nonneg hY hH) (norm_nonneg x)]
  rw [div_mul_eq_mul_div,div_mul_eq_mul_div]
  apply (le_div_iff₀ hc).mpr
  have hsmall : c*‖w-2*y*v+x‖≤a₂*‖w-2*y*v+x‖ := mul_le_mul_of_nonneg_right ha (norm_nonneg _)
  calc
    _ ≤ (2*Y+2)*H*(‖x‖+‖v‖) := by nlinarith only [hsmall,hnorm]
    _ = _ := by ring

/-- Shifting an inverse-square error by one costs at most a fixed factor four.
Use: Support.naturalWave_free_error writes all three genuine adjacent coefficient errors with the same printed denominator (m+2)^2.
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
Proof: m+2<=2*(m+1), and all original integer-shifted denominators are positive. -/
theorem inverse_square_shift (m:ℕ) : 1/((m:ℝ)+1)^2≤4/((m:ℝ)+2)^2 := by
  have hm : 0≤(m:ℝ) := Nat.cast_nonneg _
  apply (div_le_div_iff₀ (by positivity : 0<((m:ℝ)+1)^2) (by positivity : 0<((m:ℝ)+2)^2)).mpr
  nlinarith

end
end jacobi.Finite
