import jacobi.Elliptic.Quadratures
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
Article: jacobi, Theorem D.5.
The derivative is taken under the actual singular quadrature integral, with
a proved locally uniform majorant. The integral mean estimate then supplies
the strict sign; no numerical parameter sampling is involved.
Source: dominated differentiation of Lebesgue integrals.
Use: numerator of the second-moment to squared-mass ratio.
-/
namespace jacobi.Elliptic
noncomputable section
open MeasureTheory Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The mass-weighted elliptic quadrature.
Use: numerator of the second-moment to squared-mass ratio.
Article: jacobi, Theorem D.5.
-/
def kappa (t : ℝ) : ℝ := ∫ v in (0 : ℝ)..1, L t v*quadratureWeight t 0 v

/-- The literal elliptic calibration ratio.
Use: its unique inverse selects the attaining elliptic profile.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
-/
def ratio (t : ℝ) : ℝ := 2*kappa t/(3*i2 t 0^2)

/-- A calibration denominator is strictly positive at every allowed parameter pair.
Use: legitimate normalization of means and differentiation of the actual ratio.
Article: jacobi, Theorem D.5.
Proof: the integrable weight is strictly positive on the whole open integration interval. -/
theorem i2_pos {t c : ℝ} (ht : t ∈ Icc 0 1) (hc : c ∈ Icc 0 1) : 0 < i2 t c :=
  intervalIntegral.intervalIntegral_pos_of_pos_on (quadratureWeight_integrable ht hc)
    (fun v hv => div_pos (sq_pos_of_pos hv.1) (sqrt_pos.mpr (P_pos ht hc hv))) (by norm_num)

/-- The normalized shape derivative has a uniform bound away from t=1.
Use: integrable domination of the parameter derivatives, including near v=0.
Article: jacobi, Theorem D.5.
Proof: q≥(1-t)²≥(1-B)² and L≤1 on a fixed parameter subinterval. -/
theorem psi_local_bound {u B v : ℝ} (hB : B ∈ Ioo 0 1) (hu : u ∈ Icc 0 B)
    (hv : v ∈ Ioo 0 1) : 0 ≤ psi u 0 v ∧ psi u 0 v ≤ 1/(1-B)^2 := by
  -- The positive constant (1-B)² keeps the logarithmic derivative uniformly bounded.
  have huf : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1,hu.2.trans hB.2.le⟩
  have hq : 0 < q u v := by
    simpa only [r,zero_mul,add_zero] using
      (r_pos huf (by norm_num : (0 : ℝ) ∈ Icc 0 1) ⟨hv.1,hv.2.le⟩)
  have hlow : (1-B)^2 ≤ q u v := by
    have hcoef : 0 ≤ 1-u^2 := sub_nonneg.mpr (pow_le_one₀ huf.1 huf.2)
    have hv0 := hv.1
    dsimp [q]
    nlinarith [hu.2,hB.2,sq_nonneg v,mul_nonneg hcoef hv.1.le]
  have hL := L_bounds huf ⟨hv.1.le,hv.2.le⟩
  have hformula : psi u 0 v=L u v/q u v := by
    dsimp [psi,N,r]
    ring
  rw [hformula]
  exact ⟨div_nonneg (hv.1.le.trans hL.1) hq.le,
    (div_le_div_of_nonneg_right hL.2 hq.le).trans
      (div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos (sub_pos.mpr hB.2)) hlow)⟩

/-- Dominated differentiation for all affine numerators needed by the elliptic ratio.
Use: a=1,b=0 gives i_2'; a=1,b=v-1 gives kappa', without repeating analytic machinery.
Article: jacobi, Theorem D.5.
Proof: work on a parameter interval bounded above by B<1. The derivative is
bounded by (1+2/(1-B)²)/sqrt(1-v), whose integrability was proved separately. -/
theorem affine_quadrature_hasDerivAt (a b : ℝ → ℝ) (ha : Measurable a) (hb : Measurable b)
    (hab : ∀ v ∈ Ioo (0 : ℝ) 1, |a v| ≤ 1 ∧ |b v| ≤ 1)
    {t : ℝ} (ht : t ∈ Ioo 0 1) :
    IntegrableOn (fun v => (b v+(a v+t*b v)*psi t 0 v)*quadratureWeight t 0 v) (Ioo 0 1) ∧
    HasDerivAt (fun u => ∫ v in (0 : ℝ)..1, (a v+u*b v)*quadratureWeight u 0 v)
      (∫ v in (0 : ℝ)..1, (b v+(a v+t*b v)*psi t 0 v)*quadratureWeight t 0 v) t := by
  -- All exceptional endpoint values are removed by using the equal integral over (0,1).
  let B := (t+1)/2
  have hB : B ∈ Ioo (0 : ℝ) 1 := by dsimp [B]; constructor <;> linarith [ht.1,ht.2]
  have htB : t ∈ Ioo (0 : ℝ) B := ⟨ht.1,by dsimp [B]; linarith [ht.2]⟩
  let C := 1/(1-B)^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hcoeff (u v : ℝ) (hu : u ∈ Icc 0 1) (hv : v ∈ Ioo 0 1) : |a v+u*b v| ≤ 2 := by
    calc
      _ ≤ |a v|+|u*b v| := abs_add_le _ _
      _ ≤ 1+1 := add_le_add (hab v hv).1 (by
        rw [abs_mul,abs_of_nonneg hu.1]
        exact (mul_le_mul_of_nonneg_left (hab v hv).2 hu.1).trans (by simpa using hu.2))
      _ = 2 := by norm_num
  have hwm : ∀ u : ℝ, Measurable (quadratureWeight u 0) := by
    intro u
    unfold quadratureWeight P r q
    fun_prop
  have hpm : ∀ u : ℝ, Measurable (psi u 0) := by intro u; unfold psi N L r q; fun_prop
  have hmeas (u : ℝ) : AEStronglyMeasurable
      (fun v => (a v+u*b v)*quadratureWeight u 0 v) (volume.restrict (Ioo 0 1)) :=
    ((ha.add (measurable_const.mul hb)).mul (hwm u)).aestronglyMeasurable
  have hboundint := ((intervalIntegrable_iff_integrableOn_Ioo_of_le
    (by norm_num : (0 : ℝ) ≤ 1)).mp endpointWeight_integrable).const_mul (1+2*C)
  have hint : IntegrableOn (fun v => (a v+t*b v)*quadratureWeight t 0 v) (Ioo 0 1) := by
    apply (((intervalIntegrable_iff_integrableOn_Ioo_of_le
      (by norm_num : (0 : ℝ) ≤ 1)).mp endpointWeight_integrable).const_mul 2).mono' (hmeas t)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (quadratureWeight_bound ⟨ht.1.le,ht.2.le⟩
      (by norm_num) hv).1]
    exact (mul_le_mul_of_nonneg_right (hcoeff t v ⟨ht.1.le,ht.2.le⟩ hv)
      (quadratureWeight_bound ⟨ht.1.le,ht.2.le⟩ (by norm_num) hv).1).trans
      (mul_le_mul_of_nonneg_left (quadratureWeight_bound ⟨ht.1.le,ht.2.le⟩ (by norm_num) hv).2
        (by norm_num))
  have H := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioo (0 : ℝ) 1)) (s := Ioo 0 B)
    (F := fun u v => (a v+u*b v)*quadratureWeight u 0 v)
    (F' := fun u v => (b v+(a v+u*b v)*psi u 0 v)*quadratureWeight u 0 v)
    (bound := fun v => (1+2*C)*endpointWeight v)
    (isOpen_Ioo.mem_nhds htB) (Filter.Eventually.of_forall hmeas) hint
    (((hb.add ((ha.add (measurable_const.mul hb)).mul (hpm t))).mul (hwm t)).aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
      intro u hu
      have huf : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1.le,hu.2.le.trans hB.2.le⟩
      have hp := psi_local_bound hB ⟨hu.1.le,hu.2.le⟩ hv
      have hw := quadratureWeight_bound huf (by norm_num : (0 : ℝ) ∈ Icc 0 1) hv
      have hc := hcoeff u v huf hv
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hw.1]
      have hterm : |b v+(a v+u*b v)*psi u 0 v| ≤ 1+2*C := by
        calc
          _ ≤ |b v| + |a v+u*b v| * psi u 0 v := by
            simpa only [abs_mul,abs_of_nonneg hp.1] using abs_add_le (b v) ((a v+u*b v)*psi u 0 v)
          _ ≤ 1+2*C := add_le_add (hab v hv).2 (mul_le_mul hc hp.2 hp.1 (by norm_num))
      exact (mul_le_mul_of_nonneg_right hterm hw.1).trans
        (mul_le_mul_of_nonneg_left hw.2 (by positivity))) hboundint
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
      intro u hu
      have huf : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1.le,hu.2.le.trans hB.2.le⟩
      have hw := (inverse_sqrt_shape_hasDerivAt huf (by norm_num : (0 : ℝ) ∈ Icc 0 1) hv).const_mul (v^2)
      have h := ((hasDerivAt_const u (a v)).add ((hasDerivAt_id u).const_mul (b v))).mul hw
      convert h using 1
      · funext x
        dsimp [quadratureWeight]
        ring
      · dsimp [quadratureWeight]
        ring)
  refine ⟨H.1,?_⟩
  have he (u : ℝ) : (∫ v in (0 : ℝ)..1, (a v+u*b v)*quadratureWeight u 0 v) =
      ∫ v in Ioo (0 : ℝ) 1, (a v+u*b v)*quadratureWeight u 0 v := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),integral_Ioc_eq_integral_Ioo]
  simpa only [he,intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo] using H.2

 /-- The actual integral derivative of i_2.
Use: determines the sign of the elliptic ratio derivative.
Article: jacobi, Theorem D.5.
-/
def i2Slope (t : ℝ) : ℝ := ∫ v in (0 : ℝ)..1, psi t 0 v*quadratureWeight t 0 v

/-- The actual integral derivative of kappa.
Use: compares numerator and denominator changes in the calibration ratio.
Article: jacobi, Theorem D.5.
-/
def kappaSlope (t : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..1, (v-1+L t v*psi t 0 v)*quadratureWeight t 0 v

/-- Differentiation of the actual second quadrature with all domination premises proved.
Use: positivity of i_2' and the quotient rule for the calibration ratio.
Article: jacobi, Theorem D.5.
Proof: specialize dominated affine-numerator differentiation to the constant numerator one. -/
theorem i2_hasDerivAt {t : ℝ} (ht : t ∈ Ioo 0 1) :
    IntervalIntegrable (fun v => psi t 0 v*quadratureWeight t 0 v) volume 0 1 ∧
      HasDerivAt (fun u => i2 u 0) (i2Slope t) t := by
  -- The integrability conclusion is retained to justify subsequent integral comparisons.
  have h := affine_quadrature_hasDerivAt (fun _ => 1) (fun _ => 0)
    measurable_const measurable_const (fun _ _ => by norm_num) ht
  norm_num only [mul_zero,add_zero,zero_add,one_mul] at h
  exact ⟨(intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr h.1,h.2⟩

/-- Differentiation of the actual mass-weighted quadrature.
Use: the quotient rule and the strict elliptic ratio monotonicity theorem.
Article: jacobi, Theorem D.5.
Proof: specialize the common dominated theorem to L=1+t(v-1). -/
theorem kappa_hasDerivAt {t : ℝ} (ht : t ∈ Ioo 0 1) :
    IntervalIntegrable (fun v => (v-1+L t v*psi t 0 v)*quadratureWeight t 0 v) volume 0 1 ∧
      HasDerivAt kappa (kappaSlope t) t := by
  -- Both the integral and its derivative are identified with the literal printed numerator.
  have h := affine_quadrature_hasDerivAt (fun _ => 1) (fun v => v-1)
    measurable_const (measurable_id.sub measurable_const)
    (fun v hv => by
      have h1 := hv.1
      have h2 := hv.2
      constructor
      · norm_num
      · rw [abs_of_nonpos (by linarith : v-1 ≤ 0)]
        linarith) ht
  have he (u v : ℝ) : (1 : ℝ)+u*(v-1)=L u v := by dsimp [L]; ring
  simp_rw [he] at h
  exact ⟨(intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr h.1,h.2⟩

/-- The denominator quadrature increases strictly with the shape parameter.
Use: converts the mean bound into a strict sign for the calibration ratio.
Article: jacobi, Theorem D.5.
Proof: its integrable derivative weight is strictly positive throughout (0,1). -/
theorem i2Slope_pos {t : ℝ} (ht : t ∈ Ioo 0 1) : 0 < i2Slope t :=
  intervalIntegral.intervalIntegral_pos_of_pos_on (i2_hasDerivAt ht).1
    (fun v hv => mul_pos (psi_pos ⟨ht.1.le,ht.2.le⟩ (by norm_num) ⟨hv.1,hv.2.le⟩)
      (div_pos (sq_pos_of_pos hv.1)
        (sqrt_pos.mpr (P_pos ⟨ht.1.le,ht.2.le⟩ (by norm_num) hv)))) (by norm_num)

/-- The mass-weighted quadrature has mean at least two thirds.
Use: bounds the negative denominator contribution in the ratio derivative.
Article: jacobi, Theorem D.5.
Proof: L≥v pointwise, followed by the proved common integral mean estimate. -/
theorem kappa_lower {t : ℝ} (ht : t ∈ Icc 0 1) : (2/3 : ℝ)*i2 t 0 ≤ kappa t := by
  -- All factors share the same integrable positive quadrature weight.
  have hw := quadratureWeight_integrable ht (by norm_num : (0 : ℝ) ∈ Icc 0 1)
  have h := intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (0 : ℝ) ≤ 1)
    (hw.continuousOn_mul continuous_id.continuousOn)
    (hw.continuousOn_mul (show ContinuousOn (L t) (uIcc 0 1) by unfold L; fun_prop))
    (fun v hv => mul_le_mul_of_nonneg_right (L_bounds ht ⟨hv.1.le,hv.2.le⟩).1
      (quadratureWeight_bound ht (by norm_num) hv).1)
  exact (quadrature_mean_bound ht (by norm_num : (0 : ℝ) ∈ Icc 0 1)).trans h

/-- The numerator's derivative is bounded above by the denominator's derivative.
Use: a simple strict bound for the derivative of the elliptic ratio.
Article: jacobi, Theorem D.5.
Proof: compare the integrable differentiated weights pointwise using psi≥0. -/
theorem kappaSlope_le {t : ℝ} (ht : t ∈ Ioo 0 1) : kappaSlope t ≤ i2Slope t := by
  -- Positivity fixes the sign when multiplying the numerator comparison by the singular weight.
  apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (0 : ℝ) ≤ 1)
    (kappa_hasDerivAt ht).1 (i2_hasDerivAt ht).1
  intro v hv
  have hp := (psi_pos ⟨ht.1.le,ht.2.le⟩ (by norm_num : (0 : ℝ) ∈ Icc 0 1)
    ⟨hv.1,hv.2.le⟩).le
  have hL := (L_bounds ⟨ht.1.le,ht.2.le⟩ ⟨hv.1.le,hv.2.le⟩).2
  exact mul_le_mul_of_nonneg_right
    (by nlinarith [hv.2,mul_le_mul_of_nonneg_right hL hp])
    (quadratureWeight_bound ⟨ht.1.le,ht.2.le⟩ (by norm_num) hv).1

/-- Actual negative derivative of the elliptic calibration ratio.
Use: uniqueness of the elliptic shape parameter, rather than a sampled monotonicity test.
Article: jacobi, Theorem D.5.
Proof: differentiate the literal quotient. kappa≥2i_2/3, kappa'≤i_2',
and i_2,i_2'>0 give a strictly negative numerator. -/
theorem ratio_hasDerivAt_neg {t : ℝ} (ht : t ∈ Ioo 0 1) :
    ∃ d : ℝ, HasDerivAt ratio d t ∧ d < 0 := by
  -- Keep the quotient rule's exact derivative and prove its sign without numerical constants.
  have hi := (i2_hasDerivAt ht).2
  have hk := (kappa_hasDerivAt ht).2
  have hi0 := i2_pos ⟨ht.1.le,ht.2.le⟩ (by norm_num : (0 : ℝ) ∈ Icc 0 1)
  have hj := i2Slope_pos ht
  have h := (hk.const_mul 2).div ((hi.pow 2).const_mul 3) (by positivity : 3*i2 t 0^2 ≠ 0)
  refine ⟨_,h,?_⟩
  apply div_neg_of_neg_of_pos _ (show 0 < (3*i2 t 0^2)^2 by positivity)
  have hl := kappa_lower ⟨ht.1.le,ht.2.le⟩
  have hb := kappaSlope_le ht
  have hstrict : kappaSlope t*i2 t 0-2*kappa t*i2Slope t < 0 := by
    have h1 := mul_le_mul_of_nonneg_right hb hi0.le
    have h2 := mul_le_mul_of_nonneg_right hl hj.le
    nlinarith [mul_pos hi0 hj]
  have hn := mul_neg_of_pos_of_neg (show 0 < 6*i2 t 0 by positivity) hstrict
  norm_num only [Pi.pow_apply,Nat.cast_ofNat,Nat.reduceSub,pow_one]
  nlinarith

/-- Strict monotonicity of the actual elliptic calibration ratio.
Use: at most one interior elliptic parameter can satisfy a prescribed second-to-mass ratio.
Article: jacobi, Theorem D.5.
Proof: the ratio is differentiable and its proved derivative is strictly negative. -/
theorem ratio_strictAntiOn : StrictAntiOn ratio (Ioo (0 : ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo 0 1)
  · intro t ht
    obtain ⟨d,hd,_⟩ := ratio_hasDerivAt_neg ht
    exact hd.continuousAt.continuousWithinAt
  · intro t ht
    obtain ⟨d,hd,hn⟩ := ratio_hasDerivAt_neg (interior_subset ht)
    rwa [hd.deriv]

end
end jacobi.Elliptic
