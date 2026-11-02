import jacobi.Support.CauchyVolterra
import jacobi.Reference.PotentialBounds

/-!
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
The literal Cauchy action gains two powers of the endpoint coordinate
on the full bounded-growth class. This forces every candidate's ground
quotient to have the prescribed continuous endpoint value, removing the
extra regular-factor assumption from the earlier uniqueness theorem.
Use: proves endpoint regularity for every original O(t^gamma) Volterra candidate.
-/
namespace jacobi.Support
noncomputable section
open Real Set Complex Filter MeasureTheory jacobi.Reference
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The literal positive-interior Cauchy kernel has a nonsingular bound after the source growth weight is restored.
Use: proves endpoint regularity for every original O(t^gamma) Volterra candidate.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: the true ground state is positive and increasing. Bound its inverse square throughout [s,t] by its value at s, then use the genuine interval norm bound and cancel the actual positive source weight. -/
theorem groundCauchyKernel_bound {a t s:ℝ} (ha:-1<a) (ht:t∈Icc (0:ℝ) (1/2))
    (hs:s∈Ioc (0:ℝ) t) :
    ‖groundCauchyKernel a t s‖≤weight a t/weight a s*(t-s) := by
  -- The kernel itself may be singular at s=0; the estimate is made only at genuine positive source points.
  have hsp := weight_pos a ⟨hs.1,by linarith [hs.2,ht.2]⟩
  have htp := weight_pos a ⟨hs.1.trans_le hs.2,by linarith [ht.2]⟩
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := s) (b := t) (C := ((weight a s)^2)⁻¹)
    (f := fun r:ℝ => ((weight a r:ℂ)^2)⁻¹) (fun r hr => by
      rw [uIoc_of_le hs.2] at hr
      have hrp := weight_pos a ⟨hs.1.trans hr.1,by linarith [hr.2,ht.2]⟩
      have hm := groundWeight_monotone ha ⟨hs.1.le,hs.2.trans ht.2⟩
        ⟨(hs.1.trans hr.1).le,hr.2.trans ht.2⟩ hr.1.le
      rw [norm_inv,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hrp]
      exact inv_anti₀ (sq_pos_of_pos hsp) ((sq_le_sq₀ hsp.le hrp.le).mpr hm))
  rw [abs_of_nonneg (sub_nonneg.mpr hs.2)] at hh
  unfold groundCauchyKernel
  rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,
    Real.norm_eq_abs,abs_of_pos htp,abs_of_pos hsp]
  exact (mul_le_mul_of_nonneg_left hh (mul_nonneg htp.le hsp.le)).trans_eq (by field_simp)

/-- The genuine single-integral Cauchy action gains two endpoint powers on the entire ground-bounded class.
Use: every original bounded-growth candidate has a continuous normalized quotient at zero, before applying the already proved regular uniqueness theorem.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: multiply the true Cauchy-kernel bound by the actual source growth bound. Its source ground factor cancels. The remaining integrand is bounded by M*U(t)*t, whose original interval integral is at most M*U(t)*t squared. -/
theorem groundCauchyAction_bound {a:ℝ} (ha:-1<a) {v:ℝ→ℂ} {M t:ℝ} (hM:0≤M)
    (ht:t∈Icc (0:ℝ) (1/2)) (hv:∀ s∈Ioc (0:ℝ) t,‖v s‖≤M*weight a s) :
    ‖groundCauchyAction a v t‖≤M*weight a t*t^2 := by
  -- The actual kernel estimate is integrated on its true physical interval, including its null endpoint.
  have hw : 0≤weight a t := by
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h,(weight_properties ha).2.1]
    · exact (weight_pos a ⟨h,by linarith [ht.2]⟩).le
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := t) (C := M*weight a t*t)
    (f := fun s => groundCauchyKernel a t s*v s) (fun s hs => by
      rw [uIoc_of_le ht.1] at hs
      have hsp := weight_pos a ⟨hs.1,by linarith [hs.2,ht.2]⟩
      rw [norm_mul]
      have hk := groundCauchyKernel_bound ha ht hs
      have hh := mul_le_mul hk (hv s hs) (norm_nonneg _)
        (mul_nonneg (div_nonneg hw hsp.le) (sub_nonneg.mpr hs.2))
      have he : (weight a t/weight a s*(t-s))*(M*weight a s)=M*weight a t*(t-s) := by field_simp
      rw [he] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left (by linarith [hs.1] : t-s≤t) (mul_nonneg hM hw)))
  simpa only [groundCauchyAction,sub_zero,abs_of_nonneg ht.1,mul_assoc,pow_two,mul_comm,mul_left_comm] using hh

/-- The original endpoint power is bounded by a fixed positive multiple of the actual ground state on the full physical half interval.
Use: converts precisely the printed O(t^gamma) candidate class to the weight bound used in the full Volterra regularity proof.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: the original half-sine lower bound gives U(t)>=(2/pi)^gamma*t^gamma. Raise its positive-base comparison to the positive original exponent, divide by the fixed positive coefficient, and handle the zero endpoint exactly. -/
theorem endpointPower_le_weight {a:ℝ} (ha:-1<a) {t:ℝ} (ht:t∈Icc (0:ℝ) (1/2)) :
    t^(gamma a)≤(Real.pi/2)^(gamma a)*weight a t := by
  -- The coefficient is independent of the candidate and every physical coordinate.
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  by_cases ht0 : t=0
  · simp only [ht0,Real.zero_rpow hg.ne',(weight_properties ha).2.1,mul_zero,le_refl]
  have htp : 0<t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have hs := half_sine_lower ⟨htp,ht.2⟩
  have he : t≤(Real.pi/2)*(Real.sin (Real.pi*t)/Real.pi) := by
    have heq : (Real.pi/2)*(Real.sin (Real.pi*t)/Real.pi)=Real.sin (Real.pi*t)/2 := by field_simp
    rw [heq]
    linarith
  have hh := Real.rpow_le_rpow ht.1 he hg.le
  rw [Real.mul_rpow (by positivity : 0≤Real.pi/2)
    (div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg Real.pi_pos.le ht.1)
      (by nlinarith [ht.2,Real.pi_pos])) Real.pi_pos.le)] at hh
  exact hh

/-- The literal Cauchy action is genuinely integrable for every continuous regular-factor input.
Use: the final original Volterra theorem certifies convergence of its single integral in addition to the equation and uniqueness.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: the proved true triangular product integrand is integrable. Fubini gives integrability of its target-coordinate primitive. The exact triangular target identity and unchanged ground factor identify that primitive almost everywhere with the original single-kernel integrand. -/
theorem groundCauchyAction_integrable {a:ℝ} (ha:-1<a) {q:ℝ→ℂ} (hq:Continuous q)
    {t:ℝ} (ht:t∈Icc (0:ℝ) (1/2)) :
    IntervalIntegrable (fun s => groundCauchyKernel a t s*((weight a s:ℂ)*q s)) volume 0 t := by
  -- The actual source integral is identified with an integrable Fubini primitive before any equation is asserted.
  have hp : Integrable (Function.uncurry (groundTriangle a q))
      ((volume.restrict (Ioc (0:ℝ) t)).prod (volume.restrict (Ioc (0:ℝ) t))) := by
    rw [Measure.prod_restrict,← Measure.volume_eq_prod]
    simpa only [IntegrableOn,uIoc_of_le ht.1] using groundTriangle_integrable ha hq ht
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mpr
  apply (hp.integral_prod_right.const_mul (weight a t:ℂ)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [← intervalIntegral.integral_of_le ht.1]
  dsimp only [Function.uncurry]
  rw [groundTriangle_target a q ht.1 hs]
  unfold groundCauchyKernel
  ring

end
end jacobi.Support
