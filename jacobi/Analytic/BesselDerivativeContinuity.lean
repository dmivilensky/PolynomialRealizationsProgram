import jacobi.Analytic.BesselOrderContinuity
import jacobi.Bessel.OrderShift

/-!
Article: jacobi, Lemma E.1.
Use: the original simple finite-prefix zeros have uniform derivative contraction bounds on genuine product neighborhoods, so their holomorphic continuations require no root certificate.
-/
namespace jacobi.Bessel
noncomputable section
open Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual Bessel spectral derivative is jointly continuous in the original admissible order and energy.
Use: the original simple finite-prefix zeros have uniform derivative contraction bounds on genuine product neighborhoods, so their holomorphic continuations require no root certificate.
Article: jacobi, Lemma E.1.
Source: the Bessel adjacent-order differentiation identity, DLMF 10.6.2, proved earlier from the original series.
Proof: the genuine derivative is -F_(alpha+1)/(4*(alpha+1)). The shifted original Bessel function is jointly continuous by its actual common series majorant, and the true denominator is nonzero throughout the admissible half-plane. -/
theorem normalized_slope_joint_continuous :
    ContinuousOn (fun p : ℂ × ℂ => deriv (normalized p.1) p.2) {p | -1<p.1.re} := by
  -- Reuse the actual adjacent-order derivative identity for the same original Bessel function.
  intro p hp
  have hp' : -1<p.1.re := hp
  have hshift : -1<(p.1+1).re := by simp only [Complex.add_re,Complex.one_re]; linarith
  have hU : IsOpen {q : ℂ × ℂ | -1<q.1.re} := isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)
  have hF := (normalized_order_spectral_continuous.continuousAt (hU.mem_nhds hshift)).comp
    ((continuous_fst.add_const (1:ℂ)).prodMk continuous_snd).continuousAt
  have hden : (4:ℂ)*(p.1+1)≠0 := mul_ne_zero (by norm_num)
    (by simpa only [Nat.cast_zero,add_zero] using (order_nonzero hp' 0).1)
  have hcoeff : ContinuousAt (fun q : ℂ × ℂ => (-1:ℂ)/(4*(q.1+1))) p := by fun_prop
  have he : (fun q : ℂ × ℂ => (-1:ℂ)/(4*(q.1+1))*normalized (q.1+1) q.2)=ᶠ[𝓝 p]
      (fun q => deriv (normalized q.1) q.2) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact (normalized_derivative_order_shift hq q.2).symm
  exact ((hcoeff.mul hF).congr he).continuousWithinAt

end
end jacobi.Bessel
