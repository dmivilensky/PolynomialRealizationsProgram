import chebyshev1.Nonlinear.PrefixSecondOrder
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-! The long scaled-horizon prefix constant tends to π/2. -/
namespace chebyshev1.Nonlinear
noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology Interval

/-- The prefix limiting coefficient as a function of the scaled horizon. -/
def prefixSecondOrderProfile (tau : ℝ) : ℝ :=
  2*tau*prefixSecondOrderIntegral (2*tau)

theorem prefixSecondOrderIntegral_rescale {a : ℝ} (ha : a ≠ 0) :
    a*prefixSecondOrderIntegral a =
      ∫ x in (0:ℝ)..a, (1-x/a)/cosh x := by
  have hh := intervalIntegral.smul_integral_comp_mul_left
    (f := fun x : ℝ => (1-x/a)/cosh x) (a := (0:ℝ)) (b := 1) a
  simp only [smul_eq_mul, mul_zero, mul_one] at hh
  rw [← hh]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  dsimp [prefixSecondOrderIntegrand]
  rw [mul_div_cancel_left₀ x ha]

theorem prefixSecondOrderProfile_integral {tau : ℝ} (htau : 0 < tau) :
    prefixSecondOrderProfile tau =
      ∫ x in (0:ℝ)..(2*tau), (1-x/(2*tau))/cosh x :=
  prefixSecondOrderIntegral_rescale (mul_pos (by norm_num : (0:ℝ) < 2) htau).ne'

theorem prefix_secondOrderCoefficient_integral_limit {α : Type*} {l : Filter α}
    {I : α → SpectralInterval} {N : α → ℕ} {tau : ℝ} (htau : 0 < tau)
    (hK : Tendsto (fun j => (I j).kappa) l atTop)
    (hscale : Tendsto (fun j => (N j:ℝ)/sqrt (I j).kappa) l (nhds tau)) :
    Tendsto (fun j => secondOrderCoefficient Prefix.jacobiData (I j) (N j) /
      ((N j:ℝ)*sqrt (I j).kappa)) l
      (nhds (∫ x in (0:ℝ)..(2*tau), (1-x/(2*tau))/cosh x)) := by
  rw [← prefixSecondOrderProfile_integral htau]
  exact prefix_secondOrderCoefficient_limit htau hK hscale

theorem integral_sech (a : ℝ) :
    (∫ x in (0:ℝ)..a, 1/cosh x) = 2*arctan (exp a)-Real.pi/2 := by
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => 2*arctan (exp x)) (1/cosh x) x := by
    have hh := ((hasDerivAt_exp x).arctan).const_mul 2
    convert hh using 1
    rw [cosh_eq, exp_neg]
    field_simp
    ring
  have hint : IntervalIntegrable (fun x : ℝ => 1/cosh x) volume 0 a :=
    (continuous_const.div continuous_cosh (fun x => (cosh_pos x).ne')).intervalIntegrable 0 a
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) hint
  rw [exp_zero, arctan_one] at hh
  exact hh.trans (by ring)

theorem sech_le_two_exp_neg (x : ℝ) : 1/cosh x ≤ 2*exp (-x) := by
  apply (div_le_iff₀ (cosh_pos x)).mpr
  have hh : exp x ≤ 2*cosh x := by
    rw [cosh_eq]
    linarith [exp_pos (-x)]
  have hm := mul_le_mul_of_nonneg_left hh (exp_nonneg (-x))
  rw [← exp_add, neg_add_cancel, exp_zero] at hm
  nlinarith

theorem integral_mul_exp_neg (a : ℝ) :
    (∫ x in (0:ℝ)..a, x*exp (-x)) = 1-(a+1)*exp (-a) := by
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => -(x+1)*exp (-x)) (x*exp (-x)) x := by
    have hh := (((hasDerivAt_id x).add_const 1).neg).mul
      (((hasDerivAt_id x).neg).exp)
    convert hh using 1
    · rfl
    · change x*exp (-x) = -1*exp (-x) + (-(x+1))*(exp (-x)* -1)
      ring
  have hint : IntervalIntegrable (fun x : ℝ => x*exp (-x)) volume 0 a :=
    (continuous_id.mul (continuous_exp.comp continuous_neg)).intervalIntegrable 0 a
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) hint
  simp only [zero_add, neg_zero, exp_zero, mul_one] at hh
  exact hh.trans (by ring)

theorem integral_mul_sech_bounds {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ (∫ x in (0:ℝ)..a, x/cosh x) ∧ (∫ x in (0:ℝ)..a, x/cosh x) ≤ 2 := by
  have hc : Continuous (fun x : ℝ => x/cosh x) :=
    continuous_id.div continuous_cosh (fun x => (cosh_pos x).ne')
  constructor
  · exact intervalIntegral.integral_nonneg ha (fun x hx =>
      div_nonneg hx.1 (cosh_pos x).le)
  · have hb : (∫ x in (0:ℝ)..a, x/cosh x) ≤
        ∫ x in (0:ℝ)..a, 2*(x*exp (-x)) := by
      have hint2 : IntervalIntegrable (fun x : ℝ => 2*(x*exp (-x))) volume 0 a :=
        (continuous_const.mul (continuous_id.mul (continuous_exp.comp continuous_neg))).intervalIntegrable _ _
      apply intervalIntegral.integral_mono_on ha (hc.intervalIntegrable _ _)
        hint2
      intro x hx
      have hh := mul_le_mul_of_nonneg_left (sech_le_two_exp_neg x) hx.1
      calc
        _ = x*(1/cosh x) := by ring
        _ ≤ x*(2*exp (-x)) := hh
        _ = _ := by ring
    rw [intervalIntegral.integral_const_mul, integral_mul_exp_neg] at hb
    nlinarith [mul_nonneg (by linarith : 0 ≤ a+1) (exp_nonneg (-a))]

theorem prefixSecondOrderIntegral_decompose {a : ℝ} (ha : a ≠ 0) :
    a*prefixSecondOrderIntegral a = (∫ x in (0:ℝ)..a, 1/cosh x)-
      (1/a)*(∫ x in (0:ℝ)..a, x/cosh x) := by
  rw [prefixSecondOrderIntegral_rescale ha]
  have h1 : IntervalIntegrable (fun x : ℝ => 1/cosh x) volume 0 a :=
    (continuous_const.div continuous_cosh (fun x => (cosh_pos x).ne')).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun x : ℝ => (1/a)*(x/cosh x)) volume 0 a :=
    ((continuous_const.mul (continuous_id.div continuous_cosh
      (fun x => (cosh_pos x).ne')))).intervalIntegrable _ _
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub h1 h2]
  apply intervalIntegral.integral_congr
  intro x _
  ring

theorem prefixSecondOrderIntegral_infinite :
    Tendsto (fun a : ℝ => a*prefixSecondOrderIntegral a) atTop (nhds (Real.pi/2)) := by
  have hsech : Tendsto (fun a : ℝ => ∫ x in (0:ℝ)..a, 1/cosh x) atTop (nhds (Real.pi/2)) := by
    simp_rw [integral_sech]
    have hh := ((tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp tendsto_exp_atTop).const_mul 2
    simpa only [Function.comp_def, show 2*(Real.pi/2)-Real.pi/2 = Real.pi/2 by ring] using
      hh.sub_const (Real.pi/2)
  have hzero : Tendsto (fun a : ℝ => (1/a)*(∫ x in (0:ℝ)..a, x/cosh x)) atTop (nhds 0) := by
    apply squeeze_zero' _ _ (by simpa using (tendsto_const_nhds (x := (2:ℝ))).div_atTop tendsto_id)
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with a ha
      exact mul_nonneg (one_div_nonneg.mpr ha.le) (integral_mul_sech_bounds ha.le).1
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with a ha
      have hh := mul_le_mul_of_nonneg_left (integral_mul_sech_bounds ha.le).2
        (one_div_nonneg.mpr ha.le)
      simpa only [one_div_mul_eq_div] using hh
  have hh := hsech.sub hzero
  simp only [sub_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with a ha
  exact (prefixSecondOrderIntegral_decompose ha.ne').symm

theorem prefixSecondOrderProfile_infinite :
    Tendsto prefixSecondOrderProfile atTop (nhds (Real.pi/2)) :=
  prefixSecondOrderIntegral_infinite.comp (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ) < 2))

end
end chebyshev1.Nonlinear
