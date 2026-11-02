import jacobi.Hankel.JostDifferential

/-!
Article: jacobi, Lemma E.1.
These limits determine the true outgoing/incoming Wronskian and
fix the phase in the original Bessel comparison.
Use: besselAmplitudeSlope_bound and its genuine limit at infinity fix the actual Jost Wronskian, needed to identify the original Bessel solution.
-/
namespace jacobi.Hankel
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
set_option backward.isDefEq.respectTransparency false

/-- The true original outgoing Fourier slope is bounded by the actual amplitude bound on its future ray times 1/x.
Use: besselAmplitudeSlope_bound and its genuine limit at infinity fix the actual Jost Wronskian, needed to identify the original Bessel solution.
Article: jacobi, Lemma E.1.
Proof: both real-ray Fourier multipliers have unit norm. The original future integrand is bounded by G times the true inverse-square tail at x, whose exact mass is 1/x. -/
theorem outgoingSlope_ray_bound {R x G : ℝ} (hR : 0<R) (hx : R≤x)
    (f : OutgoingSpace) (hf : ∀ y : ℝ,x<y → ‖f y‖≤G) :
    ‖outgoingSlope (inverseSquare R) f x‖≤G/x := by
  -- The original Fourier tail only contains points beyond the actual spatial coordinate x.
  have hxp : 0<x := hR.trans_le hx
  have hi := (outgoingFourier_integrable (outgoingSource_integrable (inverseSquare_integrable hR) f)).integrableOn (s := Ioi x)
  have hb : ∀ᵐ (y : ℝ) ∂volume.restrict (Ioi x),
      ‖Complex.exp (2*(y:ℂ)*Complex.I)*((inverseSquare R y:ℂ)*f y)‖ ≤ inverseSquare x y*G := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hm : inverseSquare R y=inverseSquare x y := by
      rw [inverseSquare_eq (hx.trans_lt hy),inverseSquare_eq hy]
    rw [norm_mul,show 2*(y:ℂ)*Complex.I=((2*y:ℝ):ℂ)*Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I,one_mul,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (inverseSquare_nonneg hR y),hm]
    exact mul_le_mul_of_nonneg_left (hf y hy) (inverseSquare_nonneg hxp y)
  have h := (norm_integral_le_integral_norm _).trans
    (integral_mono_ae hi.norm (((inverseSquare_integrable hxp).mul_const G).integrableOn) hb)
  have hv : (∫ y in Ioi x,inverseSquare x y)=1/x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by simp [inverseSquare,hy])]
    exact inverseSquare_integral hxp
  rw [integral_mul_const,hv] at h
  rw [outgoingSlope,norm_mul,norm_neg,
    show -2*(x:ℂ)*Complex.I=((-2*x:ℝ):ℂ)*Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I,one_mul]
  exact h.trans_eq (by ring)

/-- The true original outgoing Bessel slope has its uniform inverse-first-power spatial bound on the common complex-order contraction domain.
Use: besselAmplitudeSlope_limit supplies the genuine outgoing Jost Wronskian endpoint, independent of any Bessel asymptotic premise.
Article: jacobi, Lemma E.1.
Proof: multiply the proved actual outgoing Fourier-slope tail bound by the genuine Bessel coefficient and use the original amplitude norm bound two. -/
theorem besselAmplitudeSlope_bound {R : ℝ} (hR : 0<R) {a : ℂ}
    (ha : ‖besselCoefficient a‖/R≤1/2) {x : ℝ} (hx : R≤x) :
    ‖besselAmplitudeSlope hR a x‖≤2*‖besselCoefficient a‖/x := by
  rw [besselAmplitudeSlope,norm_mul,norm_neg]
  have h := outgoingSlope_ray_bound hR hx
    (besselAmplitude hR a) (fun y _ => ((besselAmplitude hR a).norm_coe_le_norm y).trans
      (besselAmplitude_norm_le_two hR ha))
  exact (mul_le_mul_of_nonneg_left h (norm_nonneg _)).trans_eq (by ring)

/-- The actual outgoing Bessel amplitude tends to its original normalization one at infinity.
Use: the true outgoing and incoming waves have a proved nonzero Wronskian and determine the original Bessel coefficients by the real numbered-zero phase.
Article: jacobi, Lemma E.1.
Proof: its independently proved actual deviation is bounded by 2|c|/x on every later ray; the community reciprocal limit and norm squeeze prove the original limit. -/
theorem besselAmplitude_limit {R : ℝ} (hR : 0<R) {a : ℂ}
    (ha : ‖besselCoefficient a‖/R≤1/2) :
    Tendsto (fun x : ℝ => besselAmplitude hR a x) atTop (𝓝 1) := by
  have he : Tendsto (fun x : ℝ => besselAmplitude hR a x-1) atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_
      (show Tendsto (fun x : ℝ => 2*‖besselCoefficient a‖/x) atTop (𝓝 0) from
        by simpa only [div_eq_mul_inv,mul_zero] using tendsto_inv_atTop_zero.const_mul (2*‖besselCoefficient a‖))
    filter_upwards [eventually_ge_atTop R] with x hx
    exact besselAmplitude_close_to_one hR ha hx
  simpa only [sub_add_cancel,zero_add] using he.add_const (1:ℂ)

/-- The actual original outgoing Bessel slope tends to zero at infinity.
Use: together with besselAmplitude_limit, evaluates the true outgoing/incoming Wronskian rather than postulating its normalization.
Article: jacobi, Lemma E.1.
Proof: the true Fourier-tail derivative bound is at most 2|c|/x on every later ray; apply the genuine reciprocal limit and norm squeeze. -/
theorem besselAmplitudeSlope_limit {R : ℝ} (hR : 0<R) {a : ℂ}
    (ha : ‖besselCoefficient a‖/R≤1/2) :
    Tendsto (besselAmplitudeSlope hR a) atTop (𝓝 0) := by
  apply squeeze_zero_norm' ?_
    (show Tendsto (fun x : ℝ => 2*‖besselCoefficient a‖/x) atTop (𝓝 0) from
      by simpa only [div_eq_mul_inv,mul_zero] using tendsto_inv_atTop_zero.const_mul (2*‖besselCoefficient a‖))
  filter_upwards [eventually_ge_atTop R] with x hx
  exact besselAmplitudeSlope_bound hR ha hx

end
end jacobi.Hankel
