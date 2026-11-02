import jacobi.Support.ContinuumCore
import Mathlib.Analysis.ODE.Gronwall

/-!
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
The genuine sine-power ground state is increasing on the physical
half-interval. Its normalized nested Volterra operator consequently has
a direct integral norm bound. Gronwall's theorem then proves uniqueness
for the homogeneous equation with continuous regular factors. These
are the continuum uniqueness estimates used in the original complex-energy
limit, together with the actual normalized finite kernel mesh convergence.
Use: groundFlux_bound bounds the exact singular ground-weight quotient by one, providing a uniform continuum Volterra majorant without a singular endpoint hypothesis.
-/
namespace jacobi.Support
noncomputable section
open Real Set Complex Filter MeasureTheory jacobi.Reference
open scoped Topology

/-- The actual original ground sine-power weight is nondecreasing on the full physical half-interval.
Use: groundFlux_bound bounds the exact singular ground-weight quotient by one, providing a uniform continuum Volterra majorant without a singular endpoint hypothesis.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: sine is nondecreasing before pi/2 and the original exponent gamma_alpha is positive. Division by positive pi and the positive real-power map preserve that order. -/
theorem groundWeight_monotone {a:ℝ} (ha:-1<a) : MonotoneOn (weight a) (Icc (0:ℝ) (1/2)) := by
  -- The physical half-interval is the common monotonicity region of the actual original ground state.
  intro s hs t ht hst
  have hsin := Real.monotoneOn_sin
    (show π*s∈Icc (-(π/2)) (π/2) by constructor <;> nlinarith [pi_pos,hs.1,hs.2])
    (show π*t∈Icc (-(π/2)) (π/2) by constructor <;> nlinarith [pi_pos,ht.1,ht.2])
    (mul_le_mul_of_nonneg_left hst pi_pos.le)
  have hsbase : 0≤Real.sin (π*s)/π := div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
    (mul_nonneg pi_pos.le hs.1) (by nlinarith [hs.2,pi_pos])) pi_pos.le
  exact Real.rpow_le_rpow hsbase (div_le_div_of_nonneg_right hsin pi_pos.le) (by linarith [(parameters ha).1])

/-- The genuine ground-normalized first primitive in the continuum reduction of order.
Use: groundVolterra and regularWave_groundVolterra express the source Cauchy operator in its actual nested ground coordinates, without dividing the solution itself at zero.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
-/
def groundFlux (a:ℝ) (q:ℝ→ℂ) (t:ℝ) : ℂ :=
  (∫s in (0:ℝ)..t,(weight a s:ℂ)^2*q s)/(weight a t:ℂ)^2

/-- The actual normalized nested continuum Volterra operator built from the original sine-power ground state.
Use: groundVolterra_bound and groundVolterra_unique_zero give the stability and uniqueness estimates for the normalized original support-chain continuum equation.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
-/
def groundVolterra (a:ℝ) (q:ℝ→ℂ) (t:ℝ) : ℂ := ∫r in (0:ℝ)..t,groundFlux a q r

/-- The original ground-normalized primitive is bounded by the ordinary norm primitive on the complete physical half-interval.
Use: groundVolterra_bound supplies a nonsingular actual Volterra estimate suitable for Gronwall and finite-to-continuum stability.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: at zero both genuine primitives vanish. At a positive endpoint, monotonicity of the actual positive ground state bounds every squared inner weight by the endpoint ground square. The ordinary norm-of-integral inequality applies to the continuous original regular factor; divide by the genuine positive ground square and cancel it. -/
theorem groundFlux_bound {a:ℝ} (ha:-1<a) {q:ℝ→ℂ} {t:ℝ} (ht:t∈Icc (0:ℝ) (1/2))
    (hq:ContinuousOn q (Icc 0 t)) : ‖groundFlux a q t‖≤∫s in (0:ℝ)..t,‖q s‖ := by
  -- The same actual positive ground square bounds the whole original inner integration interval.
  rcases eq_or_lt_of_le ht.1 with h | h
  · subst t
    simp [groundFlux]
  have ht' : t∈Ioo 0 1 := ⟨h,by linarith [ht.2]⟩
  have hw := weight_pos a ht'
  have hbound : ‖∫s in (0:ℝ)..t,(weight a s:ℂ)^2*q s‖≤
      (weight a t)^2*(∫s in (0:ℝ)..t,‖q s‖) := by
    have hi : IntervalIntegrable (fun s:ℝ => (weight a t)^2*‖q s‖) volume 0 t :=
      (continuousOn_const.mul hq.norm).intervalIntegrable_of_Icc ht.1
    have hh := intervalIntegral.norm_integral_le_of_norm_le (f:=fun s:ℝ => (weight a s:ℂ)^2*q s) ht.1
      (Eventually.of_forall (fun s (hs:s∈Ioc (0:ℝ) t) => by
        have hs' : s∈Ioo 0 1 := ⟨hs.1,hs.2.trans_lt ht'.2⟩
        have hsw := weight_pos a hs'
        have hm := groundWeight_monotone ha ⟨hs.1.le,hs.2.trans ht.2⟩ ht hs.2
        rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hsw]
        exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ hsw.le hw.le).mpr hm) (norm_nonneg (q s)))) hi
    simpa only [intervalIntegral.integral_const_mul] using hh
  rw [groundFlux,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hw]
  exact (div_le_iff₀ (sq_pos_of_pos hw)).mpr (hbound.trans_eq (mul_comm _ _))

/-- The exact original normalized continuum Volterra operator has a nonsingular norm bound on the whole physical half-interval.
Use: groundVolterra_unique_zero obtains uniqueness at every complex energy without a small-energy or contraction-size assumption; the same bound controls the continuum residual in the finite support edge limit.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: the inner ground-normalized primitive is bounded by its ordinary norm primitive. That nonnegative primitive increases with the endpoint, so it is at most the value at the actual outer endpoint. Integrate this constant bound over the original outer interval of length t. -/
theorem groundVolterra_bound {a:ℝ} (ha:-1<a) {q:ℝ→ℂ} {t:ℝ} (ht:t∈Icc (0:ℝ) (1/2))
    (hq:ContinuousOn q (Icc 0 t)) : ‖groundVolterra a q t‖≤t*(∫s in (0:ℝ)..t,‖q s‖) := by
  -- The original nested operator is bounded on its complete triangular domain, including the singular corner.
  have hi : IntervalIntegrable (fun s:ℝ => ‖q s‖) volume 0 t := hq.norm.intervalIntegrable_of_Icc ht.1
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a:=0) (b:=t)
    (f:=groundFlux a q) (C:=∫s in (0:ℝ)..t,‖q s‖) (fun r hr => by
      rw [uIoc_of_le ht.1] at hr
      have hqr : ContinuousOn q (Icc 0 r) := hq.mono (by intro s hs; exact ⟨hs.1,hs.2.trans hr.2⟩)
      apply (groundFlux_bound ha ⟨hr.1.le,hr.2.trans ht.2⟩ hqr).trans
      exact intervalIntegral.integral_mono_interval le_rfl hr.1.le hr.2
        (Eventually.of_forall (fun s => norm_nonneg (q s))) hi)
  simpa only [groundVolterra,sub_zero,abs_of_nonneg ht.1,mul_comm] using hh

/-- The homogeneous original ground-normalized Volterra equation has only the zero continuous regular solution at every complex energy.
Use: the actual continuum solution's identification and the finite support-chain stability argument do not require a small complex energy or an assumed uniqueness certificate.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Source: Gronwall's inequality, mathlib eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right.
Proof: integrate the norm of the actual candidate to H(t). The full original Volterra estimate and the homogeneous equation give H'(t)<=abs(delta)*H(t)/2. This is a genuine ordinary derivative since the candidate is continuous. Gronwall forces H=0 from its actual initial value zero, and the same Volterra estimate then forces the original candidate itself to vanish. -/
theorem groundVolterra_unique_zero {a:ℝ} (ha:-1<a) {q:ℝ→ℂ} (hq:ContinuousOn q (Icc (0:ℝ) (1/2))) (δ:ℂ)
    (he:∀t∈Icc (0:ℝ) (1/2),q t=δ*groundVolterra a q t) :
    ∀t∈Icc (0:ℝ) (1/2),q t=0 := by
  -- The scalar norm primitive removes the singular coefficient from the uniqueness argument.
  let e (s:ℝ) := q (max 0 (min s (1/2)))
  have hec : Continuous e := hq.comp_continuous
    (continuous_const.max (continuous_id.min continuous_const))
    (fun s => ⟨le_max_left _ _,max_le (by norm_num) (min_le_right _ _)⟩)
  have heq (s:ℝ) (hs:s∈Icc (0:ℝ) (1/2)) : e s=q s := by dsimp [e]; rw [min_eq_left hs.2,max_eq_right hs.1]
  let H (t:ℝ) : ℝ := ∫s in (0:ℝ)..t,‖e s‖
  have hH (t:ℝ) : HasDerivAt H ‖e t‖ t := intervalIntegral.integral_hasDerivAt_right
    (hec.norm.intervalIntegrable 0 t) (hec.norm.stronglyMeasurableAtFilter volume (𝓝 t)) hec.norm.continuousAt
  have hHeq (t:ℝ) (ht:t∈Icc (0:ℝ) (1/2)) : (∫s in (0:ℝ)..t,‖q s‖)=H t := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    change ‖q s‖=‖e s‖
    rw [heq s ⟨hs.1,hs.2.trans ht.2⟩]
  have hpos (t:ℝ) (ht:t∈Icc (0:ℝ) (1/2)) : 0≤H t :=
    intervalIntegral.integral_nonneg_of_forall ht.1 (fun s => norm_nonneg (e s))
  have hbound (t:ℝ) (ht:t∈Icc (0:ℝ) (1/2)) : ‖q t‖≤(‖δ‖/2)*H t := by
    rw [he t ht,norm_mul]
    have hqt : ContinuousOn q (Icc 0 t) := hq.mono (by intro s hs; exact ⟨hs.1,hs.2.trans ht.2⟩)
    have hh := mul_le_mul_of_nonneg_left (groundVolterra_bound ha ht hqt) (norm_nonneg δ)
    rw [hHeq t ht] at hh
    have hsmall := mul_le_mul_of_nonneg_right ht.2 (mul_nonneg (norm_nonneg δ) (hpos t ht))
    change ‖δ‖ * ‖groundVolterra a q t‖≤_
    nlinarith only [hh,hsmall]
  have hz := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (continuous_iff_continuousAt.mpr (fun t => (hH t).continuousAt)).continuousOn
    (fun t (_:t∈Ico (0:ℝ) (1/2)) => (hH t).hasDerivWithinAt)
    (show H 0=0 by simp [H]) (fun t ht => by
      rw [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg (e t)),heq t ⟨ht.1,ht.2.le⟩,
        Real.norm_eq_abs,abs_of_nonneg (hpos t ⟨ht.1,ht.2.le⟩)]
      exact hbound t ⟨ht.1,ht.2.le⟩)
  intro t ht
  apply norm_le_zero_iff.mp
  simpa only [hz t ht,mul_zero] using hbound t ht

end
end jacobi.Support
