import jacobi.Reference.TruncatedLaplace
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
The far part of the actual defining beta integral is exponentially
small after every fixed power normalization. Its integrand may be
singular at the far endpoint: genuine integrability is sufficient.
Source: exponential domination of powers in Watson's endpoint lemma.
Use: combines with truncated_laplace_limit to evaluate the leading coefficient of the original reference beta integral, whose opposite endpoint can be singular.
-/
namespace jacobi.Reference
noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Every genuinely integrable far-end Laplace contribution is negligible after any fixed real power normalization.
Use: combines with truncated_laplace_limit to evaluate the leading coefficient of the original reference beta integral, whose opposite endpoint can be singular.
Article: jacobi, Appendix C.2 (norming ratios).
Source: the exponentially small tail estimate in Watson's lemma.
Proof: for s>=A>0 and y>=0 the exponential is at most exp(-A*y).
The norm of the true integral is bounded by that exponential times
the original integral of |h|. Every fixed y^g times that exponential
tends to zero by the community exponential-versus-power theorem. -/
theorem laplace_tail_limit {A B : ℝ} (hA : 0<A) (hAB : A≤B) (g : ℝ)
    {h : ℝ → ℝ} (hh : IntervalIntegrable h volume A B) :
    Tendsto (fun y : ℝ => y^g*(∫ s in A..B,Real.exp (-(y*s))*h s))
      atTop (𝓝 0) := by
  -- The far endpoint is handled in the actual Lebesgue integral, so its density need not be bounded.
  let C := ∫ s in A..B,‖h s‖
  have hbound (y : ℝ) (hy : 0≤y) :
      ‖∫ s in A..B,Real.exp (-(y*s))*h s‖≤Real.exp (-(A*y))*C := by
    have hm : IntervalIntegrable (fun s : ℝ => Real.exp (-(A*y))*‖h s‖) volume A B :=
      hh.norm.const_mul _
    have hb : ∀ᵐ s : ℝ, s∈Ioc A B →
        ‖Real.exp (-(y*s))*h s‖≤Real.exp (-(A*y))*‖h s‖ := by
      filter_upwards with s hs
      rw [norm_mul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith [hs.1])) (norm_nonneg _)
    have hi := intervalIntegral.norm_integral_le_of_norm_le hAB hb hm
    simpa only [intervalIntegral.integral_const_mul,C] using hi
  have hl : Tendsto (fun y : ℝ => C*(y^g*Real.exp (-(A*y)))) atTop (𝓝 0) := by
    simpa only [neg_mul,mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero g A hA).const_mul C
  apply squeeze_zero_norm' ?_ hl
  filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
  rw [norm_mul,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hy _)]
  exact (mul_le_mul_of_nonneg_left (hbound y hy.le) (Real.rpow_pos_of_pos hy _).le).trans_eq (by ring)

end
end jacobi.Reference
