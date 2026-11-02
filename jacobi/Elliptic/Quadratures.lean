import jacobi.Elliptic.Weights
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
Article: jacobi, Theorem D.5.
The quadratures below are actual Lebesgue integrals, including the integrable
square-root endpoint singularity. The common weight lemma serves both the
elliptic slice chi=0 and the Fredholm calibration in jacobi, Appendix D.
Source: the fundamental theorem of calculus and a single-crossing comparison.
Use: proves convergence and parameter continuity of all calibration integrals.
-/
namespace jacobi.Elliptic
noncomputable section
open MeasureTheory Real Set
set_option backward.isDefEq.respectTransparency false

/-- The integrable endpoint singularity used as a common quadrature majorant.
Use: proves convergence and parameter continuity of all calibration integrals.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
-/
def endpointWeight (v : ℝ) : ℝ := (sqrt (1-v))⁻¹

/-- Integrability of the common endpoint singularity, including its finite representative at one.
Use: all quadrature domination arguments use this genuine Lebesgue integrability fact.
Article: jacobi, Theorem D.5.
Proof: change v to 1-v and apply mathlib's subcritical power integrability theorem. -/
theorem endpointWeight_integrable : IntervalIntegrable endpointWeight volume 0 1 := by
  -- Reflection changes the endpoint singularity into the integrable power x^(-1/2).
  have hi : IntervalIntegrable (fun x : ℝ => x^(-(1/2 : ℝ))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hc := (hi.comp_sub_left 1).symm
  norm_num only [sub_zero,sub_self] at hc
  apply hc.congr
  intro x hx
  have hx1 : 0 ≤ 1-x := by
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    linarith [hx.2]
  change (1-x)^(-(1/2 : ℝ)) = _
  rw [Real.rpow_neg hx1,← Real.sqrt_eq_rpow]
  rfl

/-- The literal common quadrature weight, retaining both shape parameters.
Use: defines i_k and the weighted means in elliptic and Fredholm calibration.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
-/
def quadratureWeight (t c v : ℝ) : ℝ := v^2/sqrt (P t c v)

/-- Pointwise domination of the actual quadrature weight on the open unit interval.
Use: proves its integrability uniformly throughout the closed parameter square.
Article: jacobi, Theorem D.5.
Proof: sqrt(P)≥v sqrt(1-v) and v≤1. -/
theorem quadratureWeight_bound {t c v : ℝ} (ht : t ∈ Icc 0 1) (hc : c ∈ Icc 0 1)
    (hv : v ∈ Ioo 0 1) : 0 ≤ quadratureWeight t c v ∧
      quadratureWeight t c v ≤ endpointWeight v := by
  -- The lower polynomial bound removes one factor v from the square-root denominator.
  have hs := sqrt_pos.mpr (P_pos ht hc hv)
  have he := sqrt_pos.mpr (sub_pos.mpr hv.2)
  have hp := sqrt_le_sqrt (P_bounds ht hc ⟨hv.1.le,hv.2.le⟩).1
  rw [sqrt_mul (sub_nonneg.mpr hv.2.le),sqrt_sq hv.1.le] at hp
  constructor
  · exact div_nonneg (sq_nonneg v) hs.le
  · dsimp [quadratureWeight,endpointWeight]
    apply (div_le_iff₀ hs).mpr
    rw [inv_mul_eq_div]
    apply (le_div_iff₀ he).mpr
    have h : v^2*sqrt (1-v) ≤ v*sqrt (1-v) :=
      mul_le_mul_of_nonneg_right (by nlinarith [hv.1,hv.2]) he.le
    exact h.trans (by simpa only [mul_comm] using hp)

/-- Absolute integrability of the common weight for every allowed parameter pair.
Use: the integrals defining calibration parameters are genuine, finite quadratures.
Article: jacobi, Theorem D.5.
Proof: dominate on the open interval by the proved endpoint majorant; endpoints are null. -/
theorem quadratureWeight_integrable {t c : ℝ} (ht : t ∈ Icc 0 1) (hc : c ∈ Icc 0 1) :
    IntervalIntegrable (quadratureWeight t c) volume 0 1 := by
  -- Null endpoints permit domination solely where P is strictly positive.
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
  have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le
    (by norm_num : (0 : ℝ) ≤ 1)).mp endpointWeight_integrable
  apply hi.mono'
  · have hm : Measurable (quadratureWeight t c) := by unfold quadratureWeight P r q; fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    rw [Real.norm_eq_abs,abs_of_nonneg (quadratureWeight_bound ht hc hv).1]
    exact (quadratureWeight_bound ht hc hv).2

/-- Separating the endpoint singularity from the smooth relative weight.
Use: single-crossing comparison gives the integral mean bound.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
Proof: factor sqrt((1-v)r) and cancel its positive factors. -/
theorem quadratureWeight_factor {t c v : ℝ} (hv : v ∈ Ioo 0 1) :
    quadratureWeight t c v = endpointWeight v*(v^2/sqrt (r t c v)) := by
  dsimp [quadratureWeight,endpointWeight,P]
  rw [sqrt_mul (sub_nonneg.mpr hv.2.le)]
  ring

/-- The relative weight v²/sqrt(r) is increasing despite the cubic Fredholm term.
Use: proves Weights (b) by comparison with the elementary endpoint distribution.
Article: jacobi, Theorem D.5.
Proof: its derivative has positive numerator 2v²+3(1-t²)v+4(1-t)²+ctv³. -/
theorem relativeWeight_strictMonoOn {t c : ℝ} (ht : t ∈ Icc 0 1) (hc : c ∈ Icc 0 1) :
    StrictMonoOn (fun v => v^2/sqrt (r t c v)) (Ioo 0 1) := by
  -- All coefficients of the derivative numerator are nonnegative, and 2v² is positive.
  have hd (v : ℝ) (hv : v ∈ Ioo 0 1) :
      HasDerivAt (fun z => z^2/sqrt (r t c z))
        (v*(2*v^2+3*(1-t^2)*v+4*(1-t)^2+c*t*v^3)/
          (2*r t c v*sqrt (r t c v))) v := by
    have hr := r_pos ht hc ⟨hv.1,hv.2.le⟩
    have hpoly : HasDerivAt (r t c) (2*v+(1-t^2)+3*c*t*v^2) v := by
      convert ((((hasDerivAt_id v).pow 2).add
        ((hasDerivAt_id v).const_mul (1-t^2))).add_const ((1-t)^2)).add
        (((hasDerivAt_id v).pow 3).const_mul (c*t)) using 1 <;>
        (first | rfl | (dsimp [r,q]; ring))
    convert ((hasDerivAt_id v).pow 2).div (hpoly.sqrt hr.ne') (sqrt_pos.mpr hr).ne' using 1
    · rfl
    · dsimp only [id_eq]
      field_simp
      rw [sq_sqrt hr.le]
      dsimp [r,q]
      ring
  apply strictMonoOn_of_deriv_pos (convex_Ioo 0 1)
  · exact fun v hv => (hd v hv).continuousAt.continuousWithinAt
  · intro v hv
    have hv' : v ∈ Ioo (0 : ℝ) 1 := interior_subset hv
    rw [(hd v hv').deriv]
    have ht0 := ht.1
    have hc0 := hc.1
    have htv : 0 ≤ 1-t^2 := by nlinarith [ht.2,sq_nonneg (1-t)]
    have hnum : 0 < 2*v^2+3*(1-t^2)*v+4*(1-t)^2+c*t*v^3 := by
      have hv0 := hv'.1
      positivity
    exact div_pos (mul_pos hv'.1 hnum)
      (mul_pos (mul_pos (by norm_num) (r_pos ht hc ⟨hv'.1,hv'.2.le⟩))
        (sqrt_pos.mpr (r_pos ht hc ⟨hv'.1,hv'.2.le⟩)))

/-- The second elliptic quadrature, or its common Fredholm extension.
Use: normalization of mass and of the weighted probability measure.
Article: jacobi, Theorem D.5.
-/
def i2 (t c : ℝ) : ℝ := ∫ v in (0 : ℝ)..1, quadratureWeight t c v

/-- The third elliptic quadrature, or its common Fredholm extension.
Use: energy formula and the mean in Weights (b).
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
-/
def i3 (t c : ℝ) : ℝ := ∫ v in (0 : ℝ)..1, v*quadratureWeight t c v

/-- The elementary endpoint distribution has mean exactly two thirds.
Use: reference distribution for the single-crossing proof of Weights (b).
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
Proof: the integrand is the derivative of -(2/3)v sqrt(1-v), whose endpoint values vanish. -/
theorem endpointWeight_centered :
    (∫ v in (0 : ℝ)..1, (v-2/3)*endpointWeight v) = 0 := by
  -- The primitive is continuous at the singular endpoint; its derivative is needed only inside.
  let F (v : ℝ) := -(2/3 : ℝ)*v*sqrt (1-v)
  have hd (v : ℝ) (hv : v ∈ Ioo 0 1) :
      HasDerivAt F ((v-2/3)*endpointWeight v) v := by
    have hp : 0 < 1-v := sub_pos.mpr hv.2
    have h := ((hasDerivAt_id v).const_mul (-(2/3 : ℝ))).mul
      (((hasDerivAt_id v).const_sub 1).sqrt hp.ne')
    convert h using 1
    · rfl
    · dsimp only [endpointWeight,id_eq]
      field_simp
      nlinarith [sq_sqrt hp.le]
  have hi := endpointWeight_integrable.continuousOn_mul
    (show ContinuousOn (fun v : ℝ => v-2/3) (uIcc 0 1) by fun_prop)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (0 : ℝ) ≤ 1) (f := F) (by dsimp [F]; fun_prop) hd hi
  norm_num [F] at he
  exact he

/-- The common calibration weight has mean at least two thirds.
Use: the sign estimate in strict elliptic ratio monotonicity and the Fredholm quadratures.
Article: jacobi, Theorem D.5.
Proof: v²/sqrt(r) is increasing, so its value at 2/3 yields a lower comparison
on both sides of that point. The comparison's integral is exactly zero. -/
theorem quadrature_mean_bound {t c : ℝ} (ht : t ∈ Icc 0 1) (hc : c ∈ Icc 0 1) :
    (2/3 : ℝ)*i2 t c ≤ i3 t c := by
  -- A single crossing replaces the article's separate numerical bounds on two subintervals.
  let h (v : ℝ) := v^2/sqrt (r t c v)
  let a : ℝ := 2/3
  have ha : a ∈ Ioo (0 : ℝ) 1 := by norm_num [a]
  have hmono := (relativeWeight_strictMonoOn ht hc).monotoneOn
  have hb := endpointWeight_integrable.continuousOn_mul
    (show ContinuousOn (fun v : ℝ => v-a) (uIcc 0 1) by fun_prop)
  have hw := quadratureWeight_integrable ht hc
  have hi := hw.continuousOn_mul
    (show ContinuousOn (fun v : ℝ => v-a) (uIcc 0 1) by fun_prop)
  have hcompare := intervalIntegral.integral_mono_on_of_le_Ioo
    (by norm_num : (0 : ℝ) ≤ 1) (hb.const_mul (h a)) hi (fun v hv => by
      have hn : 0 ≤ endpointWeight v := inv_nonneg.mpr (sqrt_nonneg _)
      rw [quadratureWeight_factor hv]
      change h a*((v-a)*endpointWeight v) ≤ (v-a)*(endpointWeight v*h v)
      rcases le_total v a with hvle | hvge
      · have hh : h v ≤ h a := hmono hv ha hvle
        nlinarith [mul_nonneg (sub_nonneg.mpr hh)
          (mul_nonneg (sub_nonneg.mpr hvle) hn)]
      · have hh : h a ≤ h v := hmono ha hv hvge
        nlinarith [mul_nonneg (sub_nonneg.mpr hh)
          (mul_nonneg (sub_nonneg.mpr hvge) hn)])
  rw [intervalIntegral.integral_const_mul] at hcompare
  have hzero : (∫ v in (0 : ℝ)..1, (v-a)*endpointWeight v)=0 := endpointWeight_centered
  rw [hzero,mul_zero] at hcompare
  have hvi := hw.continuousOn_mul
    (show ContinuousOn (fun v : ℝ => v) (uIcc 0 1) from continuous_id.continuousOn)
  have he : (∫ v in (0 : ℝ)..1, (v-a)*quadratureWeight t c v) = i3 t c-a*i2 t c := by
    simp only [sub_mul]
    rw [intervalIntegral.integral_sub hvi (hw.const_mul a),intervalIntegral.integral_const_mul]
    rfl
  rw [he] at hcompare
  exact sub_nonneg.mp hcompare

end
end jacobi.Elliptic
