import jacobi.Hankel.FrequencyBounds
import jacobi.Analysis.DerivativeFromValues

/-!
Article: jacobi, Lemma E.1.
Thus propagation into complex frequency uses genuine initial Cauchy
data, rather than assuming a differentiated Hankel expansion.
Use: frequencyError_initialSlope invokes the real unit-interval derivative estimate with actual restrictions of the same original complex error.
-/
namespace jacobi.Hankel
noncomputable section
open Set
set_option backward.isDefEq.respectTransparency false

/-- The actual complex Bessel error and slope have their genuine first two real derivatives at every positive real frequency.
Use: frequencyError_initialSlope invokes the real unit-interval derivative estimate with actual restrictions of the same original complex error.
Article: jacobi, Lemma E.1.
Proof: restrict each independently proved original complex-frequency derivative along the genuine real inclusion, whose true derivative is one. -/
theorem frequencyError_real_derivatives {R : ℝ} (hR : 0<R) (a : ℂ) {x : ℝ} (hx : 0<x) :
    HasDerivAt (fun t : ℝ => frequencyError hR a (t:ℂ)) (frequencyErrorSlope hR a (x:ℂ)) x ∧
      HasDerivAt (fun t : ℝ => frequencyErrorSlope hR a (t:ℂ)) (frequencyErrorCurvature hR a (x:ℂ)) x := by
  -- Restriction uses the genuine complex derivative and the real inclusion's derivative one.
  have hz := Complex.ofReal_mem_slitPlane.mpr hx
  have hd : HasDerivAt (fun t : ℝ => (t:ℂ)) 1 x := by
    simpa only [Function.comp_def,id_eq,Complex.ofRealCLM_apply,Complex.ofReal_one] using
      Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_id x)
  constructor
  · convert! (frequencyError_hasDerivAt hR a hz).comp x hd using 1
    simp only [mul_one]
  · convert! (frequencyErrorSlope_hasDerivAt hR a hz).comp x hd using 1
    simp only [mul_one]

/-- The actual original Bessel error has a true cubic initial slope bound from its genuine value estimate and original quartic forcing.
Use: uniform_bessel_frequency_strip discharges the value and forcing bounds uniformly on the same original complex-order disk before propagating the true Cauchy state to complex frequency.
Article: jacobi, Lemma E.1.
Proof: on [x,x+1], the actual cubic value bound is at most C/x^3. The genuine error ODE bounds its curvature by ((1+B)*C+D)/x^3, since x>=1 turns the original quartic forcing into the same cubic majorant. Apply the proved unit-interval value/curvature slope estimate and collect the original constants. -/
theorem frequencyError_initialSlope {R : ℝ} (hR : 0<R) {a : ℂ} (ha : -1<a.re)
    {B C D : ℝ} (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hc : ‖besselCoefficient a‖≤B)
    (hv : ∀ t : ℝ,R<t → ‖frequencyError hR a (t:ℂ)‖≤C/t^3)
    (hs : ∀ t : ℝ,1≤t → ‖frequencyHankelResidual a (t:ℂ)‖≤D/t^4)
    {x : ℝ} (hx : R<x) (hx1 : 1≤x) :
    ‖frequencyErrorSlope hR a (x:ℂ)‖≤((3+B)*C+D)/x^3 := by
  -- The initial slope estimate is obtained from actual values of the true error on one original unit interval.
  have hxp : 0<x := lt_of_lt_of_le zero_lt_one hx1
  have hval (t : ℝ) (ht : t∈Icc x (x+1)) : ‖frequencyError hR a (t:ℂ)‖≤C/x^3 :=
    (hv t (hx.trans_le ht.1)).trans (by gcongr; exact ht.1)
  have hcurv (t : ℝ) (ht : t∈Icc x (x+1)) :
      ‖frequencyErrorCurvature hR a (t:ℂ)‖≤((1+B)*C+D)/x^3 := by
    have ht1 : 1≤t := hx1.trans ht.1
    have htp : 0<t := lt_of_lt_of_le zero_lt_one ht1
    have h34 : t^3≤t^4 := by nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (pow_nonneg htp.le 3)]
    have hsrc : ‖frequencyHankelResidual a (t:ℂ)‖≤D/x^3 :=
      (hs t ht1).trans ((div_le_div_of_nonneg_left hD (pow_pos htp 3) h34).trans (by gcongr; exact ht.1))
    have hpot := frequency_potential_bound (z := (t:ℂ)) hc ht1
    have hh := frequencyError_curvature_bound hR ha (Complex.ofReal_ne_zero.mpr htp.ne') hpot hsrc
    exact (hh.trans (add_le_add (mul_le_mul_of_nonneg_left (hval t ht) (by positivity)) le_rfl)).trans_eq (by ring)
  have hh := jacobi.Analysis.slope_bound_from_values
    (x := x) (M := C/x^3) (N := ((1+B)*C+D)/x^3) (by positivity)
    (fun t ht => (frequencyError_real_derivatives hR a (hxp.trans_le ht.1)).1)
    (fun t ht => (frequencyError_real_derivatives hR a (hxp.trans_le ht.1)).2) hval hcurv
  exact hh.trans_eq (by ring)

end
end jacobi.Hankel
