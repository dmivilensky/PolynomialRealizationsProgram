import nesterov.Flow.SpreadAnalysis

/-!
Article: Appendix B, the explicit bound |V(x)| ≤ 8/x in the spread proof.
Use: retain the integral of the variable derivative bound after integration by
parts, giving the source constant rather than a coarser uniform estimate.
-/
namespace nesterov.Flow
noncomputable section
open Set intervalIntegral

theorem abs_spreadV_le_eight {x : ℝ} (hx : 0<x) : |spreadV x|≤8/x := by
  have hxn : x≠0 := ne_of_gt hx
  have hu (lam : ℝ) : HasDerivAt (fun y : ℝ=>y^2) (2*lam) lam := by
    simpa using hasDerivAt_pow 2 lam
  have hv (lam : ℝ) : HasDerivAt (fun y : ℝ=>Real.sin (y*x)/x) (Real.cos (lam*x)) lam := by
    simpa [mul_div_cancel_right₀ _ hxn] using
      (((hasDerivAt_id' lam).mul_const x).sin.div_const x)
  have hh := integral_mul_deriv_eq_deriv_mul (a:=(1:ℝ)) (b:=2)
    (fun lam _=>hu lam) (fun lam _=>hv lam)
    ((by fun_prop : Continuous (fun lam : ℝ=>2*lam)).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun lam : ℝ=>Real.cos (lam*x))).intervalIntegrable _ _)
  change spreadV x=2^2*(Real.sin (2*x)/x)-1^2*(Real.sin (1*x)/x)-
    ∫ lam in (1:ℝ)..2,(2*lam)*(Real.sin (lam*x)/x) at hh
  have hi : |∫ lam in (1:ℝ)..2,(2*lam)*(Real.sin (lam*x)/x)|≤3/x := by
    apply (abs_integral_le_integral_abs (by norm_num : (1:ℝ)≤2)).trans
    calc
      _ ≤ ∫ lam in (1:ℝ)..2,(2*lam)/x := by
        apply integral_mono_on (by norm_num : (1:ℝ)≤2)
          ((by fun_prop : Continuous (fun lam : ℝ=>|(2*lam)*(Real.sin (lam*x)/x)|)).intervalIntegrable _ _)
          ((by fun_prop : Continuous (fun lam : ℝ=>(2*lam)/x)).intervalIntegrable _ _)
        intro lam hlam
        rw [abs_mul,abs_of_nonneg (by linarith [hlam.1] : 0≤2*lam),abs_div,abs_of_pos hx,←mul_div_assoc]
        apply (div_le_div_iff_of_pos_right hx).mpr
        have hpos : 0≤2*lam := by linarith [hlam.1]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (lam*x)) hpos
      _ = 3/x := by rw [integral_div,integral_const_mul,integral_id];norm_num
  rw [hh]
  calc
    _ ≤ |(2:ℝ)^2*(Real.sin (2*x)/x)-1^2*(Real.sin (1*x)/x)|+
      |∫ lam in (1:ℝ)..2,(2*lam)*(Real.sin (lam*x)/x)| := abs_sub _ _
    _ ≤ (4/x+1/x)+3/x := by
      apply add_le_add _ hi
      apply (abs_sub _ _).trans
      simp only [abs_mul,abs_div,abs_of_pos hx]
      norm_num
      rw [←mul_div_assoc,←add_div,←one_div x,←add_div]
      exact (div_le_div_iff_of_pos_right hx).mpr
        (by linarith [Real.abs_sin_le_one (2*x),Real.abs_sin_le_one x])
    _ = _ := by ring

end
end nesterov.Flow
