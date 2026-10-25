import chebyshev1.SineJacobi.ConvolutionLimit
import chebyshev1.SineJacobi.ProfileDerivatives
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
Article: chebyshev1, Theorem E.3.
The limiting convolution is the complete elliptic integral appearing in E.3.
Use: `chebyshev1.SineJacobi.convolutionIntegral_eq_elliptic` feeds
`chebyshev1.SineJacobi.endpoint_scaled_limit` (Direct endpoint asymptotics with the exact
normalization of E.3).
-/
namespace chebyshev1.SineJacobi
noncomputable section
open Real Set MeasureTheory

/--
Defines `ellipticSubstitution` of type `ℝ` by `1/2+arcsin (k*sin theta)/T`.

Use:
`_private.chebyshev1.SineJacobi.ConvolutionElliptic.0.chebyshev1.SineJacobi.substitution_integrand`
uses this definition to establish the identity stated in that declaration.

Article: chebyshev1, Theorem 5.1 via `chebyshev1.SineJacobi.sineIntegral_eq`.
-/
private def ellipticSubstitution (T k theta : ℝ) : ℝ := 1/2+arcsin (k*sin theta)/T
/--
Defines `ellipticSubstitution₁` of type `ℝ` by `k*cos theta/(T*sqrt (1-k^2*sin theta^2))`.

Use:
`_private.chebyshev1.SineJacobi.ConvolutionElliptic.0.chebyshev1.SineJacobi.substitution_deriv`
uses this definition to establish the actual derivative at the stated point: `HasDerivAt
(ellipticSubstitution T k) (ellipticSubstitution₁ T k theta) theta`.

Article: chebyshev1, Theorem 5.1 via `chebyshev1.SineJacobi.sineIntegral_eq`.
-/
private def ellipticSubstitution₁ (T k theta : ℝ) : ℝ :=
  k*cos theta/(T*sqrt (1-k^2*sin theta^2))

/--
The actual derivative at the stated point: `HasDerivAt (ellipticSubstitution T k)
(ellipticSubstitution₁ T k theta) theta`.

Use: `chebyshev1.SineJacobi.convolutionIntegral_eq_elliptic` uses this derivative formula
to establish the identity `convolutionIntegral t = (2/Real.pi)*ellipticK (sin
(Real.pi*t/2))`.

Article: chebyshev1, Theorem 5.1 via `chebyshev1.SineJacobi.sineIntegral_eq`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
private theorem substitution_deriv {T k : ℝ} (hk : |k| < 1) (theta : ℝ) :
    HasDerivAt (ellipticSubstitution T k) (ellipticSubstitution₁ T k theta) theta := by
  -- Apply
  -- `_private.chebyshev1.SineJacobi.ConvolutionElliptic.0.chebyshev1.SineJacobi.ellipticSubstitution₁`
  -- to the displayed hypotheses, then match the resulting expression to the goal.
  have hab : |k*sin theta| < 1 := by
    rw [abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg k) (abs_sin_le_one theta)).trans_lt hk
  have hh := abs_lt.mp hab
  have hd := (((hasDerivAt_arcsin (by linarith) (by linarith)).comp theta
    ((hasDerivAt_sin theta).const_mul k)).div_const T).const_add (1/2)
  convert hd using 1
  · rfl
  · unfold ellipticSubstitution₁
    simp only [mul_pow]
    ring

/--
Membership in the specified domain/enclosure: `ellipticSubstitution (Real.pi*t) (sin
(Real.pi*t/2)) theta ∈ Icc (0:ℝ) 1`.

Use:
`_private.chebyshev1.SineJacobi.ConvolutionElliptic.0.chebyshev1.SineJacobi.substitution_integrand`
uses this assertion to establish the identity stated in that declaration.

Article: chebyshev1, Theorem 5.1 via `chebyshev1.SineJacobi.sineIntegral_eq`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
private theorem substitution_range {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) (theta : ℝ) :
    ellipticSubstitution (Real.pi*t) (sin (Real.pi*t/2)) theta ∈ Icc (0:ℝ) 1 := by
  -- Apply
  -- `_private.chebyshev1.SineJacobi.ConvolutionElliptic.0.chebyshev1.SineJacobi.ellipticSubstitution`
  -- to the displayed hypotheses, then match the resulting expression to the goal.
  have hT := mul_pos pi_pos ht.1
  have hhalf : Real.pi*t/2 ∈ Icc (-(Real.pi/2)) (Real.pi/2) := by
    constructor <;> nlinarith [pi_pos, ht.1, ht.2]
  have hk : 0 ≤ sin (Real.pi*t/2) :=
    (sin_pos_of_mem_Ioo ⟨by linarith, by nlinarith [pi_pos, ht.2]⟩).le
  have hu := arcsin_le_arcsin (mul_le_of_le_one_right hk (sin_le_one theta))
  have hl := arcsin_le_arcsin (mul_le_mul_of_nonneg_left (neg_one_le_sin theta) hk)
  rw [arcsin_sin' hhalf] at hu
  simp only [mul_neg, mul_one, arcsin_neg, arcsin_sin' hhalf] at hl
  unfold ellipticSubstitution
  constructor
  · have hh : -(1/2:ℝ) ≤ arcsin (sin (Real.pi*t/2)*sin theta)/(Real.pi*t) :=
      (le_div_iff₀ hT).mpr (by linarith [hl])
    linarith
  · have hh : arcsin (sin (Real.pi*t/2)*sin theta)/(Real.pi*t) ≤ (1/2:ℝ) :=
      (div_le_iff₀ hT).mpr (by linarith [hu])
    linarith

/--
Exact identity `convolutionKernel t (ellipticSubstitution (Real.pi*t) (sin (Real.pi*t/2))
theta)* ellipticSubstitution₁ (Real.pi*t) (sin (Real.pi*t/2)) theta = (1/Real.pi)*(1/sqrt
(1-sin (Real.pi*t/2)^2*sin theta^2))`.

Use: `chebyshev1.SineJacobi.convolutionIntegral_eq_elliptic` uses this identity to
establish exact identity `convolutionIntegral t = (2/Real.pi)*ellipticK (sin (Real.pi*t/2))`.

Article: chebyshev1, Theorem 5.1 via `chebyshev1.SineJacobi.sineIntegral_eq`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
private theorem substitution_integrand {t theta : ℝ} (ht : t ∈ Ioo (0:ℝ) 1)
    (hth : theta ∈ Ioo (-(Real.pi/2)) (Real.pi/2)) :
    convolutionKernel t (ellipticSubstitution (Real.pi*t) (sin (Real.pi*t/2)) theta)*
      ellipticSubstitution₁ (Real.pi*t) (sin (Real.pi*t/2)) theta =
        (1/Real.pi)*(1/sqrt (1-sin (Real.pi*t/2)^2*sin theta^2)) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  let T := Real.pi*t
  let k := sin (Real.pi*t/2)
  let u := ellipticSubstitution T k theta
  have hT : 0 < T := mul_pos pi_pos ht.1
  have hk : 0 < k := sin_pos_of_mem_Ioo
    ⟨by dsimp [T] at hT; linarith,
      by nlinarith [pi_pos, ht.2]⟩
  have hk1 : |k| < 1 := by simpa only [k, profileModulus] using profileModulus_lt_one ht
  have hc : 0 < cos theta := cos_pos_of_mem_Ioo hth
  have hr := substitution_range ht theta
  change u ∈ Icc (0:ℝ) 1 at hr
  have hsin : 0 ≤ sin (Real.pi*(t*u)) := by
    apply sin_nonneg_of_mem_Icc
    constructor
    · exact mul_nonneg pi_pos.le (mul_nonneg ht.1.le hr.1)
    · nlinarith [pi_pos, ht.1, ht.2, hr.1, hr.2]
  have harg1 : Real.pi*(t*u) = T/2+arcsin (k*sin theta) := by
    dsimp [u, ellipticSubstitution]
    dsimp [T]
    field_simp [ht.1.ne']
  have harg2 : Real.pi*(t*(1-u)) = T/2-arcsin (k*sin theta) := by
    dsimp [u, ellipticSubstitution]
    dsimp [T]
    field_simp [ht.1.ne']; ring
  have hab : |k*sin theta| < 1 := by
    rw [abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg k) (abs_sin_le_one theta)).trans_lt hk1
  have hprod : sin (Real.pi*(t*u))*sin (Real.pi*(t*(1-u))) = (k*cos theta)^2 := by
    rw [harg1, harg2, mul_comm, sin_shift_product]
    rw [sin_arcsin (abs_lt.mp hab).1.le (abs_lt.mp hab).2.le]
    have he : sin (T/2) = k := by dsimp [T, k]
    rw [he]
    nlinarith [sin_sq_add_cos_sq theta]
  have hroot : sqrt (sin (Real.pi*(t*u)))*sqrt (sin (Real.pi*(t*(1-u)))) = k*cos theta := by
    rw [← sqrt_mul hsin, hprod, sqrt_sq (mul_pos hk hc).le]
  have hden : sqrt (1-k^2*sin theta^2) ≠ 0 :=
    (sqrt_pos.mpr (elliptic_den_pos k theta hk1)).ne'
  change convolutionKernel t u*ellipticSubstitution₁ T k theta = _
  unfold convolutionKernel ellipticSubstitution₁
  rw [hroot]
  change t/(k*cos theta)*(k*cos theta/(T*sqrt (1-k^2*sin theta^2))) =
    (1/Real.pi)*(1/sqrt (1-k^2*sin theta^2))
  dsimp only [T]
  generalize sqrt (1-k^2*sin theta^2) = r at hden ⊢
  field_simp [hk.ne', hc.ne', hT.ne', hden, ht.1.ne', pi_pos.ne']

/--
The limiting convolution is the complete elliptic integral appearing in E.3.

Exact identity `convolutionIntegral t = (2/Real.pi)*ellipticK (sin (Real.pi*t/2))`.

Use: `chebyshev1.SineJacobi.endpoint_scaled_limit` rewrites with this identity to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun a =>
endpoint (N a) (s a)/sqrt (Real.pi*(N a:ℝ))) l (𝓝 (sineProfile t))`.

Article: chebyshev1, Theorem 5.1 via `chebyshev1.SineJacobi.sineIntegral_eq`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem convolutionIntegral_eq_elliptic {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    convolutionIntegral t = (2/Real.pi)*ellipticK (sin (Real.pi*t/2)) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  let T := Real.pi*t
  let k := sin (Real.pi*t/2)
  have hT : 0 < T := mul_pos pi_pos ht.1
  have hk1 : |k| < 1 := by simpa only [k, profileModulus] using profileModulus_lt_one ht
  have hk : 0 < k := sin_pos_of_mem_Ioo
    ⟨by dsimp [T] at hT; linarith,
      by nlinarith [pi_pos, ht.2]⟩
  have hend1 : ellipticSubstitution T k (-(Real.pi/2)) = 0 := by
    unfold ellipticSubstitution
    rw [sin_neg, sin_pi_div_two, mul_neg, mul_one, arcsin_neg]
    dsimp [k, T]
    rw [arcsin_sin (by nlinarith [pi_pos, ht.1]) (by nlinarith [pi_pos, ht.2])]
    field_simp [ht.1.ne']
    ring
  have hend2 : ellipticSubstitution T k (Real.pi/2) = 1 := by
    unfold ellipticSubstitution
    rw [sin_pi_div_two, mul_one]
    dsimp [k, T]
    rw [arcsin_sin (by nlinarith [pi_pos, ht.1]) (by nlinarith [pi_pos, ht.2])]
    field_simp [ht.1.ne']
    ring
  have hs := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := -(Real.pi/2)) (b := Real.pi/2)
    (f := ellipticSubstitution T k) (f' := ellipticSubstitution₁ T k)
    (g := convolutionKernel t)
    (show ContinuousOn (ellipticSubstitution T k) _ from by unfold ellipticSubstitution; fun_prop)
    (fun theta _ => substitution_deriv hk1 theta)
    (fun theta hth => by
      rw [min_eq_left (by linarith [pi_pos] : -(Real.pi/2) ≤ Real.pi/2),
        max_eq_right (by linarith [pi_pos] : -(Real.pi/2) ≤ Real.pi/2)] at hth
      unfold ellipticSubstitution₁
      exact div_nonneg (mul_nonneg hk.le (cos_pos_of_mem_Ioo hth).le)
        (mul_nonneg hT.le (sqrt_nonneg _)))
  rw [hend1, hend2] at hs
  unfold convolutionIntegral
  rw [← hs]
  have hi : (∫ theta in -(Real.pi/2)..Real.pi/2,
      (convolutionKernel t ∘ ellipticSubstitution T k) theta*ellipticSubstitution₁ T k theta) =
      ∫ theta in -(Real.pi/2)..Real.pi/2,
        (1/Real.pi)*(1/sqrt (1-k^2*sin theta^2)) := by
    apply intervalIntegral.integral_congr_uIoo
    intro theta hth
    rw [uIoo_of_le (by linarith [pi_pos] : -(Real.pi/2) ≤ Real.pi/2)] at hth
    exact substitution_integrand ht hth
  rw [hi, intervalIntegral.integral_const_mul]
  let F : ℝ → ℝ := fun theta => 1/sqrt (1-k^2*sin theta^2)
  have hF := (elliptic_integrand_continuous k hk1).intervalIntegrable
    (μ := volume) (-(Real.pi/2)) 0
  have hF' := (elliptic_integrand_continuous k hk1).intervalIntegrable
    (μ := volume) 0 (Real.pi/2)
  rw [← intervalIntegral.integral_add_adjacent_intervals hF hF']
  have he : (∫ theta in -(Real.pi/2)..0, F theta) = ∫ theta in (0:ℝ)..Real.pi/2, F theta := by
    have hh := intervalIntegral.integral_comp_neg (f := F) (a := (0:ℝ)) (b := Real.pi/2)
    simpa only [F, sin_neg, neg_sq, neg_zero] using hh.symm
  change (1/Real.pi)*((∫ theta in -(Real.pi/2)..0, F theta)+
    (∫ theta in (0:ℝ)..Real.pi/2, F theta)) = _
  rw [he]
  change (1/Real.pi)*(ellipticK k+ellipticK k) = _
  ring

end
end chebyshev1.SineJacobi
