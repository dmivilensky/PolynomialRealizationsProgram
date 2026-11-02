import jacobi.Variational.GreenSpatialBound
import jacobi.Variational.DominatedPrimitive

/-!
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
The actual regularized determinant equals the integral of 1-1/(2g)-s*m.
The genuine spectral and spatial parameter derivatives have the same actual
Green trace. A proved common integrable majorant supplies spatial convergence,
closed-interval continuity and differentiation. The zero-parameter values
are both zero, so the ordinary mean value theorem fixes the constant.
Source: the proved operator trace calculus and dominated Bochner differentiation.
Use: discharges every analytic interchange and endpoint premise in the determinant integral identity.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Filter Set chebyshev2.Continuum
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The actual spatial determinant integrals converge, vary continuously up to zero, and have their genuine interior parameter derivatives.
Use: discharges every analytic interchange and endpoint premise in the determinant integral identity.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: the actual upper endpoint Green-ratio source gives one integrable
majorant for all pointwise derivatives. The integrand is zero at zero.
Apply the proved dominated primitive theorem with actual measurable Green families. -/
theorem L1Source.greenSpatialIntegral_calculus (m : L1Source) (hc : Continuous m.value) {b : ℝ}
    (hb : 0<b) (hp : b*observe m .top<1) :
    (∀ t∈Icc (0:ℝ) b,Integrable (m.greenSpatialIntegrand t)) ∧
      ContinuousOn (fun t => ∫ x,m.greenSpatialIntegrand t x) (Icc (0:ℝ) b) ∧
      ∀ t∈Ioo (0:ℝ) b,HasDerivAt (fun u => ∫ x,m.greenSpatialIntegrand u x)
        (∫ x,m.greenSpatialDerivative t x) t := by
  -- The same actual spectral pole margin controls the whole closed interval.
  have htop := (kernelSpectralData m.integrable m.nonneg).eigenvalue_nonneg 0
  have hmargin (t : ℝ) (ht : t∈Icc (0:ℝ) b) : t*observe m .top<1 :=
    (mul_le_mul_of_nonneg_right ht.2 htop).trans_lt hp
  apply dominated_parameter_primitive m.greenSpatialIntegrand m.greenSpatialDerivative
    (m.greenSpatialMajorant b hb.le hp) hb m.greenSpatialIntegrand_zero
    (fun x t ht => m.greenSpatialIntegrand_hasDerivAt ht.1 (hmargin t ht) x)
    (m.greenSpatialDerivative_bound hc hb.le hp) (m.greenSpatialMajorant_integrable hc hb.le hp)
  · intro t ht
    unfold L1Source.greenSpatialIntegrand
    simp_rw [m.greenParameter_eq ht.1 (hmargin t ht)]
    have hg : Continuous (fun x => 2*m.fredholmGreen t ht.1 (hmargin t ht) x x) := continuous_const.mul
      ((m.fredholmGreen_continuous ht.1 (hmargin t ht)).comp (continuous_id.prodMk continuous_id))
    exact ((continuous_const.sub (hg.inv₀ (fun x => mul_ne_zero (by norm_num)
      (m.fredholmGreen_pos ht.1 (hmargin t ht) x x).ne'))).sub (hc.const_mul t)).aestronglyMeasurable
  · intro t ht
    exact (m.greenSpatialDerivative_trace hc ht.1 (hmargin t ht)).1.aestronglyMeasurable

/-- The actual regularized determinant equals its exact spatial Green-diagonal integral, with convergence proved.
Use: supplies equation (Dg) for the true inverse diagonal in the Fredholm calibration.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: on a slightly larger subcritical parameter interval, dominated
integration gives the genuine spatial derivative. Its proved Green trace
equals the actual spectral series derivative. The difference is continuous
at zero, has zero derivative inside, and has zero initial value; the mean
value theorem therefore gives the stated actual equality. -/
theorem L1Source.fredholm_spatial_integral (m : L1Source) (hc : Continuous m.value) {s : ℝ}
    (hs : 0≤s) (hp : s*observe m .top<1) :
    Integrable (fun x => 1-(2*m.fredholmGreen s hs hp x x)⁻¹-s*m.value x) ∧
      m.fredholmReal s=(∫ x,1-(2*m.fredholmGreen s hs hp x x)⁻¹-s*m.value x) ∧
      m.fredholm s=ENNReal.ofReal (∫ x,1-(2*m.fredholmGreen s hs hp x x)⁻¹-s*m.value x) := by
  -- A genuine larger subcritical endpoint supplies all convergence and continuity data before comparison.
  let Λ := observe m .top
  have hΛ : 0≤Λ := (kernelSpectralData m.integrable m.nonneg).eigenvalue_nonneg 0
  let b := s+(1-s*Λ)/(2*(Λ+1))
  have hbs : s<b := by
    dsimp only [b]
    exact lt_add_of_pos_right s (div_pos (sub_pos.mpr hp) (by positivity))
  have hb : 0<b := lt_of_le_of_lt hs hbs
  have hbp : b*observe m .top<1 := by
    have he : 2*(Λ+1)*(b-s)=1-s*Λ := by dsimp only [b]; field_simp; ring
    have hstep : 0≤b-s := sub_nonneg.mpr hbs.le
    change b*Λ<1
    nlinarith
  obtain ⟨hFi,hcont,hderiv⟩ := m.greenSpatialIntegral_calculus hc hb hbp
  have hmargin (t : ℝ) (ht : t∈Icc (0:ℝ) b) : t*observe m .top<1 :=
    (mul_le_mul_of_nonneg_right ht.2 hΛ).trans_lt hbp
  let J (t : ℝ) := ∫ x,m.greenSpatialIntegrand t x
  have hJ0 : J 0=0 := by simp only [J,m.greenSpatialIntegrand_zero,integral_zero]
  have hD0 : m.fredholmReal 0=0 := by simp only [L1Source.fredholmReal,fredholmLog,zero_mul,sub_zero,log_one,neg_zero,tsum_zero]
  have heq : m.fredholmReal s=J s := by
    by_cases hs0 : s=0
    · rw [hs0,hD0,hJ0]
    · have hsp : 0<s := lt_of_le_of_ne hs (Ne.symm hs0)
      let f (t : ℝ) := J t-m.fredholmReal t
      have hfc : ContinuousOn f (Icc (0:ℝ) s) := hcont.mono
        (show Icc (0:ℝ) s⊆Icc (0:ℝ) b from fun _ ht => ⟨ht.1,ht.2.trans hbs.le⟩) |>.sub
          (fun t ht => (m.fredholmReal_hasDerivAt ht.1
            (hmargin t ⟨ht.1,ht.2.trans hbs.le⟩)).continuousAt.continuousWithinAt)
      have hfd (t : ℝ) (ht : t∈Ioo (0:ℝ) s) : HasDerivAt f 0 t := by
        have htB : t∈Ioo (0:ℝ) b := ⟨ht.1,ht.2.trans hbs⟩
        have hpt := hmargin t ⟨htB.1.le,htB.2.le⟩
        have hJ := hderiv t htB
        rw [(m.greenSpatialDerivative_trace hc htB.1.le hpt).2] at hJ
        convert! hJ.sub (m.fredholmReal_green_hasDerivAt htB.1.le hpt) using 1
        exact (sub_self _).symm
      obtain ⟨t,ht,hmean⟩ := exists_deriv_eq_slope f hsp hfc
        (fun t ht => (hfd t ht).differentiableAt.differentiableWithinAt)
      rw [(hfd t ht).deriv] at hmean
      have hz : f s=f 0 := by
        have hh := (div_eq_zero_iff).mp hmean.symm
        exact sub_eq_zero.mp (hh.resolve_right (by simpa only [sub_zero] using hsp.ne'))
      dsimp only [f] at hz
      rw [hJ0,hD0] at hz
      linarith
  have htarget : m.greenSpatialIntegrand s=fun x => 1-(2*m.fredholmGreen s hs hp x x)⁻¹-s*m.value x := by
    funext x
    unfold L1Source.greenSpatialIntegrand
    rw [m.greenParameter_eq hs hp]
  have hfinite := hFi s ⟨hs,hbs.le⟩
  rw [htarget] at hfinite
  have heq' : m.fredholmReal s=(∫ x,1-(2*m.fredholmGreen s hs hp x x)⁻¹-s*m.value x) := by
    simpa only [J,htarget] using heq
  exact ⟨hfinite,heq',by rw [m.fredholm_eq hs (sub_pos.mpr hp) (by linarith),heq']⟩

end
end jacobi.Variational
