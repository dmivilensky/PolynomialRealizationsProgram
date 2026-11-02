import jacobi.Fredholm.Moments

/-!
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
The covariance sign and the positive-response comparison are proved for
the original convergent singular integrals. They provide the two decisive
energy-to-mass derivative signs, including the full-support parameter.
Source: Chebyshev's integral inequality, proved here by centering at the true mean,
and the common elliptic mean bound from jacobi, .
Use: the true normalized coordinate mean belongs to (0,1], licensing the covariance centering point.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory jacobi.Elliptic
set_option backward.isDefEq.respectTransparency false

/-- The actual third state moment is positive and at most the second state moment.
Use: the true normalized coordinate mean belongs to (0,1], licensing the covariance centering point.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
Proof: the common mean bound gives positivity and v<=1 gives the upper bound under the genuine integral. -/
theorem state_mean_bounds {t c : ℝ} (ht : t∈Icc (0:ℝ) 1) (hc : c∈Icc (0:ℝ) 1) :
    0< i3 t c ∧ i3 t c≤ i2 t c := by
  have hi := quadratureWeight_integrable ht hc
  have hpos := i2_pos ht hc
  have hmean := quadrature_mean_bound ht hc
  refine ⟨by linarith,?_⟩
  exact intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (0:ℝ)≤1)
    (hi.continuousOn_mul continuous_id.continuousOn) hi
    (fun v hv => (mul_le_mul_of_nonneg_right hv.2.le (quadratureWeight_bound ht hc hv).1).trans_eq (one_mul _))

/-- The genuine shape-response covariance has the exact nonpositive sign needed for the Fredholm shape ratio.
Use: proves mean_3(psi)<=mean_2(psi) without a sampled sign or an unproved probability inequality.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
Proof: center v at its actual weighted mean a=I3/I2. Since psi is
decreasing, (a-v)*(psi(v)-psi(a))>=0 pointwise. Integrate its equivalent
linear comparison; the centered terms cancel exactly by a*I2=I3. -/
theorem shape_covariance {t c : ℝ} (ht : t∈Ioc (0:ℝ) 1) (hc : c∈Icc (0:ℝ) 1) :
    shape3 t c*i2 t c≤shape2 t c*i3 t c := by
  -- The centering value is an actual positive normalized mean of this same singular weight.
  have ht' : t∈Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2⟩
  have hi := quadratureWeight_integrable ht' hc
  have hsi := shape_integrable ht' hc
  have h2 := i2_pos ht' hc
  have h3 := state_mean_bounds ht' hc
  let a := i3 t c/i2 t c
  have ha : a∈Ioc (0:ℝ) 1 := ⟨div_pos h3.1 h2,(div_le_one h2).mpr h3.2⟩
  have hcancel : a*i2 t c=i3 t c := div_mul_cancel₀ _ h2.ne'
  have hright := ((hsi.1.const_mul a).add
    ((hi.continuousOn_mul continuous_id.continuousOn).const_mul (psi t c a))).sub
    (hi.const_mul (a*psi t c a))
  have hh := intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (0:ℝ)≤1) hsi.2 hright
    (fun v hv => by
      have hw := (quadratureWeight_bound ht' hc hv).1
      dsimp only [id_eq]
      have hsign : 0≤(a-v)*(psi t c v-psi t c a) := by
        rcases le_total v a with hvle | hale
        · exact mul_nonneg (sub_nonneg.mpr hvle) (sub_nonneg.mpr
            ((psi_strictAntiOn ht hc).antitoneOn ⟨hv.1,hv.2.le⟩ ha hvle))
        · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hale) (sub_nonpos.mpr
            ((psi_strictAntiOn ht hc).antitoneOn ha ⟨hv.1,hv.2.le⟩ hale))
      nlinarith [mul_nonneg hsign hw])
  rw [intervalIntegral.integral_sub ((hsi.1.const_mul a).add
      ((hi.continuousOn_mul continuous_id.continuousOn).const_mul (psi t c a)))
      (hi.const_mul (a*psi t c a)),
    intervalIntegral.integral_add (hsi.1.const_mul a)
      ((hi.continuousOn_mul continuous_id.continuousOn).const_mul (psi t c a)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hh
  change shape3 t c≤a*shape2 t c+psi t c a*i3 t c-(a*psi t c a)*i2 t c at hh
  have hbound : shape3 t c≤a*shape2 t c := by
    nlinarith [congrArg (fun r : ℝ => psi t c a*r) hcancel]
  have hm := mul_le_mul_of_nonneg_right hbound h2.le
  nlinarith [congrArg (fun r : ℝ => shape2 t c*r) hcancel]

/-- The true positive determinant response has the normalized mean comparison of the source.
Use: proves nonnegative chi derivative of the energy-to-mass shape ratio.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
Proof: v<=1 and h>=0 give response3<=response2. The common verified
mean bound gives I2<=3*I3/2, and all factors are nonnegative. -/
theorem response_mean_bound {t c : ℝ} (ht : t∈Icc (0:ℝ) 1) (hc : c∈Icc (0:ℝ) 1) :
    response3 t c*i2 t c≤(3/2:ℝ)*response2 t c*i3 t c := by
  -- Only convergent actual integrals occur in the mean comparison.
  have hi := response_integrable ht hc
  have hnon : 0≤response2 t c := by
    rw [response2,intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),integral_Ioc_eq_integral_Ioo]
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    exact mul_nonneg (h_bounds ht hc hv).1 (quadratureWeight_bound ht hc hv).1
  have hh : response3 t c≤response2 t c :=
    intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (0:ℝ)≤1) hi.2 hi.1
      (fun v hv => (mul_le_mul_of_nonneg_right hv.2.le
        (mul_nonneg (h_bounds ht hc hv).1 (quadratureWeight_bound ht hc hv).1)).trans_eq (one_mul _))
  have hmean := quadrature_mean_bound ht hc
  have h1 := mul_le_mul_of_nonneg_right hh (i2_pos ht hc).le
  have h2 := mul_le_mul_of_nonneg_left hmean hnon
  nlinarith

end
end jacobi.Fredholm
