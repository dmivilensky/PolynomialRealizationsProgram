import jacobi.Reference.CosineDomination
import Mathlib.Analysis.Calculus.MeanValue

/-!
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
On an actual bounded complex-frequency disc, sine and the exponential
increment have linear bounds and the cosine increment has a quadratic
bound. These are genuine estimates for the original entire functions.
Source: the mean-value inequality on convex sets and the double-angle identity.
Use: cosine_quadratic_bound controls the genuine Volterra energy at the support envelope's transition index.
-/
namespace jacobi.Complex
noncomputable section
open Real Set

/-- The original complex sine has a uniform linear bound on every actual bounded frequency disc.
Use: cosine_quadratic_bound controls the genuine Volterra energy at the support envelope's transition index.
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
Source: the complex mean-value inequality and the exact exponential cosine bound.
Proof: the sine derivative is the genuine cosine, whose norm is at most exp(L) throughout the convex closed frequency disc. Compare the original sine value to its true zero value at the origin. -/
theorem sine_linear_bound {L:ℝ} (hL:0≤L) {z:ℂ} (hz:‖z‖≤L) :
    ‖_root_.Complex.sin z‖≤exp L*‖z‖ := by
  -- The derivative bound holds on the same actual disc joining the origin to the original frequency.
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜:=ℂ) (x:=(0:ℂ)) (y:=z)
    (f:=_root_.Complex.sin)
    (fun w (_hw:w∈Metric.closedBall (0:ℂ) L) => (_root_.Complex.hasDerivAt_sin w).differentiableAt)
    (fun w hw => by
      rw [(_root_.Complex.hasDerivAt_sin w).deriv]
      exact (jacobi.Reference.cosine_norm_bound w).trans (exp_le_exp.mpr
        ((_root_.Complex.abs_im_le_norm w).trans (by simpa only [Metric.mem_closedBall,dist_zero_right] using hw))))
    (convex_closedBall (0:ℂ) L) (by simpa only [Metric.mem_closedBall,dist_self] using hL)
    (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz)
  simpa only [_root_.Complex.sin_zero,sub_zero] using hh

/-- The actual complex cosine increment is quadratically bounded on every genuine bounded frequency disc.
Use: the original support transition-state Volterra energy is uniformly bounded when (m+1)*|theta| is bounded.
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
Source: the exact complex cosine double-angle identity and the proved linear sine bound.
Proof: cos(z)-1=-2*sin(z/2)^2. The actual half-frequency remains in the same bounded disc, and its sine has the proved linear bound; square that bound and retain a common constant. -/
theorem cosine_quadratic_bound {L:ℝ} (hL:0≤L) {z:ℂ} (hz:‖z‖≤L) :
    ‖_root_.Complex.cos z-1‖≤(2*(exp L)^2)*‖z‖^2 := by
  -- The exact double-angle factor supplies both powers of the genuine small frequency.
  have hzhalf : ‖z/2‖≤‖z‖ := by rw [norm_div,_root_.Complex.norm_ofNat]; nlinarith [norm_nonneg z]
  have hs := (sine_linear_bound hL (hzhalf.trans hz)).trans (mul_le_mul_of_nonneg_left hzhalf (exp_pos L).le)
  have hid : _root_.Complex.cos z-1=(-2)*(_root_.Complex.sin (z/2))^2 := by
    have h := _root_.Complex.cos_two_mul_eq_one_sub (z/2)
    rw [show (2:ℂ)*(z/2)=z by ring] at h
    linear_combination h
  rw [hid,norm_mul,norm_pow]
  norm_num only [norm_neg,_root_.Complex.norm_ofNat]
  have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (exp_pos L).le (norm_nonneg z))).mpr hs
  nlinarith only [hsq]

/-- The actual complex exponential increment has a uniform linear bound on every genuine bounded frequency disc.
Use: the original two-component oscillatory state at the true transition index is bounded by the proved polynomial value and first-difference bounds.
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
Source: the complex mean-value inequality and the exact norm of the exponential.
Proof: on the convex closed disc the original exponential derivative has norm exp(Re z)<=exp(L). Compare to its exact value one at zero. -/
theorem exponential_increment_bound {L:ℝ} (hL:0≤L) {z:ℂ} (hz:‖z‖≤L) :
    ‖_root_.Complex.exp z-1‖≤exp L*‖z‖ := by
  -- The same genuine frequency disc controls the entire exponential and its actual derivative.
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜:=ℂ) (x:=(0:ℂ)) (y:=z)
    (f:=_root_.Complex.exp)
    (fun w (_hw:w∈Metric.closedBall (0:ℂ) L) => (_root_.Complex.hasDerivAt_exp w).differentiableAt)
    (fun w hw => by
      rw [(_root_.Complex.hasDerivAt_exp w).deriv,_root_.Complex.norm_exp]
      exact exp_le_exp.mpr ((_root_.Complex.re_le_norm w).trans
        (by simpa only [Metric.mem_closedBall,dist_zero_right] using hw)))
    (convex_closedBall (0:ℂ) L) (by simpa only [Metric.mem_closedBall,dist_self] using hL)
    (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz)
  simpa only [_root_.Complex.exp_zero,sub_zero] using hh

end
end jacobi.Complex
