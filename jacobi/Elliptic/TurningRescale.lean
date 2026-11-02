import jacobi.Elliptic.StateIntegrals
import jacobi.Elliptic.RatioEndpoints

/-!
Article: jacobi, Theorem D.5.
The actual turning data Y=t^(-2), sigma=t^(-2)-t^(-3) transform the cubic
first integral exactly into Q_t=P(t,0,.). The genuine I_2, I_3 and J
integrals acquire the printed powers of the turning height. Endpoint values
are excluded only on null singletons, so every identity is a Lebesgue one.
Source: affine change of variables and the positive square-root scaling law.
Use: implements y=Y*v in each actual turning-height elliptic quadrature.
-/
namespace jacobi.Elliptic
noncomputable section
open MeasureTheory Real Filter Set
set_option backward.isDefEq.respectTransparency false

/-- A positive dilation maps the open unit interval integral to its exact scaled open interval.
Use: implements y=Y*v in each actual turning-height elliptic quadrature.
Article: jacobi, Theorem D.5.
Proof: use the exact interval-integral dilation formula and remove its null endpoints. -/
theorem integral_rescale_positive {c : ℝ} (hc : 0<c) (f : ℝ → ℝ) :
    (∫ y in Ioo (0:ℝ) c,f y)=c*(∫ v in Ioo (0:ℝ) 1,f (c*v)) := by
  have h := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1) f c
  simp only [smul_eq_mul,mul_zero,mul_one] at h
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le hc.le,integral_Ioc_eq_integral_Ioo] at h
  exact h.symm

/-- The normalized turning cubic is exactly the common elliptic weight polynomial.
Use: identifies the actual ODE quadratures with the already analyzed i_2, i_3 and kappa.
Article: jacobi, Theorem D.5.
Proof: substitute Y=t^(-2), sigma=t^(-2)-t^(-3), and expand the rational polynomial. -/
theorem turning_cubic_rescale {t : ℝ} (ht : 0<t) (v : ℝ) :
    (((t⁻¹)^2*v-((t⁻¹)^2-(t⁻¹)^3))^2-((t⁻¹)^2*v)^3)=
      (t⁻¹)^6*P t 0 v := by
  unfold P r q
  field_simp
  ring

/-- The positive square root in the actual Jacobian has its exact t^(-3) factor.
Use: fixes the square-root branch in every rescaled elliptic integral.
Article: jacobi, Theorem D.5.
Proof: the cubic identity gives a square positive scalar factor; use the real square-root product law. -/
theorem turning_sqrt_rescale {t : ℝ} (ht : 0<t) (v : ℝ) :
    sqrt (((t⁻¹)^2*v-((t⁻¹)^2-(t⁻¹)^3))^2-((t⁻¹)^2*v)^3)=
      (t⁻¹)^3*sqrt (P t 0 v) := by
  rw [turning_cubic_rescale ht,show (t⁻¹)^6=((t⁻¹)^3)^2 by ring,
    Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by positivity : 0≤(t⁻¹)^3)]

/-- The actual turning-height mass and energy quadratures equal their unit-interval counterparts.
Use: eliminates the ODE peak from the exact elliptic moment and energy formulas.
Article: jacobi, Theorem D.5.
Proof: scale the open turning interval by Y=t^(-2), substitute the proved
square-root identity, and collect the exact scalar factors inside the integral. -/
theorem state_integrals_rescale {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    stateIntegral ((t⁻¹)^2-(t⁻¹)^3) ((t⁻¹)^2) 2=(t⁻¹)^3*i2 t 0 ∧
      stateIntegral ((t⁻¹)^2-(t⁻¹)^3) ((t⁻¹)^2) 3=(t⁻¹)^5*i3 t 0 := by
  -- The target square root is strictly positive on the open unit interval.
  have htpos := ht.1
  have hscale : 0<(t⁻¹)^2 := by positivity
  have hsqrt (v : ℝ) (hv : v∈Ioo (0:ℝ) 1) : sqrt (P t 0 v)≠0 :=
    (sqrt_pos.mpr (P_pos ⟨ht.1.le,ht.2.le⟩ (by norm_num) hv)).ne'
  constructor
  · rw [stateIntegral,integral_rescale_positive hscale,i2,
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),integral_Ioc_eq_integral_Ioo,
      ← integral_const_mul,← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro v hv
    dsimp only
    rw [turning_sqrt_rescale ht.1]
    unfold quadratureWeight
    field_simp [ht.1.ne',hsqrt v hv]
  · rw [stateIntegral,integral_rescale_positive hscale,i3,
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),integral_Ioc_eq_integral_Ioo,
      ← integral_const_mul,← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro v hv
    dsimp only
    rw [turning_sqrt_rescale ht.1]
    unfold quadratureWeight
    field_simp [ht.1.ne',hsqrt v hv]

/-- The actual mixed turning-height quadrature has the printed unit-interval factor.
Use: identifies the actual second-moment to mass-square ratio with r(t).
Article: jacobi, Theorem D.5.
Proof: the same positive dilation and square-root scaling apply, while
y-sigma=t^(-3)*L(t,v) supplies the extra mixed factor. -/
theorem state_mixed_rescale {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    stateMixedIntegral ((t⁻¹)^2-(t⁻¹)^3) ((t⁻¹)^2)=(t⁻¹)^6*kappa t := by
  -- Positivity of the actual quadrature weight licenses the interior cancellation.
  have htpos := ht.1
  rw [stateMixedIntegral,integral_rescale_positive (by positivity : 0<(t⁻¹)^2),kappa,
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),integral_Ioc_eq_integral_Ioo,
    ← integral_const_mul,← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro v hv
  dsimp only
  rw [turning_sqrt_rescale ht.1]
  have hsqrt : sqrt (P t 0 v)≠0 :=
    (sqrt_pos.mpr (P_pos ⟨ht.1.le,ht.2.le⟩ (by norm_num) hv)).ne'
  unfold quadratureWeight L
  field_simp [ht.1.ne',hsqrt]
  ring

end
end jacobi.Elliptic
