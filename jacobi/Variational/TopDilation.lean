import jacobi.Variational.StrictDilation
import jacobi.Young.H1Scaling
import chebyshev2.GroundState.RegularGround

/-!
Article: jacobi, Lemma D.3.
A positive actual L2 maximizing vector is rescaled unitarily. Its Rayleigh
pairing is the same exponential integral already used for G_2, with source
sqrt(m)*f. The source has proved positive mass, so concentration has a
strictly positive linear gain for every nonzero integrable density.
Source: the Birman--Schwinger Rayleigh principle and unitary Lebesgue dilation.
Use: tests the concentrated density operator against the original top vector in the rescaled coordinates.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Filter chebyshev2.Continuum chebyshev2.Sobolev
open chebyshev2.GroundState
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- The unitary spatial dilation on the physical L2 space.
Use: tests the concentrated density operator against the original top vector in the rescaled coordinates.
Article: jacobi, Lemma D.3.
-/
def physicalDilation (f : FeatureSpace) (t : ℝ) (ht : 0<t) : FeatureSpace :=
  ((jacobi.Young.memLp_two_scale (Lp.memLp f) ht.ne').const_mul (sqrt t)).toLp
    (fun x => sqrt t*f (t*x))

/-- The actual L2 dilation has the displayed representative almost everywhere.
Use: computes its norm and its actual kernel pairing without identifying representatives pointwise.
Article: jacobi, Lemma D.3.
Proof: use the defining Lp representative theorem for the proved rescaled L2 function. -/
theorem physicalDilation_coe (f : FeatureSpace) {t : ℝ} (ht : 0<t) :
    physicalDilation f t ht=ᵐ[volume] fun x => sqrt t*f (t*x) :=
  ((jacobi.Young.memLp_two_scale (Lp.memLp f) ht.ne').const_mul (sqrt t)).coeFn_toLp

/-- The physical spatial dilation is unitary at every positive scale.
Use: the rescaled top vector remains an admissible unit Rayleigh test vector.
Article: jacobi, Lemma D.3.
Proof: square the norm, use the a.e. representative formula, and cancel t against its Lebesgue Jacobian. -/
theorem physicalDilation_norm (f : FeatureSpace) {t : ℝ} (ht : 0<t) :
    ‖physicalDilation f t ht‖=‖f‖ := by
  -- Norm equality is proved in the genuine L2 quotient, independently of representatives.
  have he : ‖physicalDilation f t ht‖^2=‖f‖^2 := by
    rw [l2_norm_sq,l2_norm_sq]
    calc
      _ = ∫ x,t*(f (t*x))^2 := integral_congr_ae
        ((physicalDilation_coe f ht).mono fun x hx => by rw [hx,mul_pow,Real.sq_sqrt ht.le])
      _ = _ := by
        rw [integral_const_mul,Measure.integral_comp_mul_left (fun x => f x^2),
          abs_of_pos (inv_pos.mpr ht),smul_eq_mul,← mul_assoc,mul_inv_cancel₀ ht.ne',one_mul]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he

/-- Every actual physical Rayleigh pairing is the literal exponential source pairing.
Use: compares the original and concentrated operators using the same source-level tangent estimate.
Article: jacobi, Lemma D.3.
Proof: the actual kernel representative formula gives the iterated integral;
absolute convergence of the source product licenses Fubini and all a.e. replacements. -/
theorem kernel_laplace_pairing (m : L1Source) (f : FeatureSpace) {j : ℝ → ℝ}
    (hj : Integrable j) (hjm : Measurable j)
    (he : (fun x => sqrt (m.value x)*f x)=ᵐ[volume] j) :
    inner ℝ f (kernelOperator m.integrable m.nonneg f)=laplacePair j 1 1 := by
  -- The signed L1 source, not any pointwise choice of an L2 class, controls Fubini.
  rw [L2.inner_def,laplacePair,
    integral_prod _ (laplace_integrable hj hjm (by norm_num : (0:ℝ)≤1) zero_lt_one)]
  apply integral_congr_ae
  filter_upwards [kernelOperator_coe m.integrable m.nonneg f,he] with x hx hxe
  change kernelOperator m.integrable m.nonneg f x*f x=_
  rw [hx]
  have hinner : (∫ y,exp (-|x-y|)*sqrt (m.value y)*f y)=∫ y,exp (-|x-y|)*j y := by
    apply integral_congr_ae
    filter_upwards [he] with y hy
    rw [mul_assoc,hy]
  rw [hinner]
  calc
    _ = (sqrt (m.value x)*f x)*(∫ y,exp (-|x-y|)*j y) := by ring
    _ = j x*(∫ y,exp (-|x-y|)*j y) := by rw [hxe]
    _ = ∫ y,j x*(exp (-|x-y|)*j y) := (integral_const_mul _ _).symm
    _ = _ := integral_congr_ae (Eventually.of_forall fun y => by
      dsimp only
      simp only [one_mul,div_one]
      ring)

/-- The actual leading eigenvalue has a strictly positive local concentration gain.
Use: verifies the top constraint's strict dilation direction in the multiplier theorem.
Article: jacobi, Lemma D.3.
Proof: dilate a proved nonnegative unit top eigenvector. Its nonzero source
has a strictly positive tangent integral; the actual Rayleigh upper bound
for the concentrated operator gives the claimed uniform gain on 1<=t<=2. -/
theorem top_strict_dilation (m : L1Source) (hm : 0<m.mass) :
    ∃ k : ℝ,0<k ∧ ∀ (t : ℝ) (ht : 1≤t),t≤2 →
      observe m .top+k*(t-1)≤observe (m.dilate t (by linarith)) .top := by
  -- All spectral and positivity inputs come from the actual maximizing vector.
  obtain ⟨f,hf,hfn,he⟩ := exists_nonnegative_maximizer m.integrable m.nonneg hm
  let j (x : ℝ) := |sqrt (m.value x)*f x|
  have hj : Integrable j := (synthesis_coefficient_integrable m.integrable m.nonneg f).abs
  have hjm : Measurable j := continuous_abs.measurable.comp
    ((m.measurable.sqrt).mul (Lp.stronglyMeasurable f).measurable)
  have hjn (x : ℝ) : 0≤j x := abs_nonneg _
  have hje : (fun x => sqrt (m.value x)*f x)=ᵐ[volume] j :=
    hfn.mono fun x hx => (abs_of_nonneg (mul_nonneg (sqrt_nonneg _) hx)).symm
  have hjp : 0<∫ x,j x := by
    rw [← integral_congr_ae hje]
    exact maximizer_source_positive m.integrable m.nonneg hm hf hfn he
  have hpair : laplacePair j 1 1=observe m .top := by
    rw [← kernel_laplace_pairing m f hj hjm hje,he,real_inner_smul_right,
      real_inner_self_eq_norm_sq,hf,one_pow,mul_one]
    rfl
  let C := laplaceGain j 1
  have hC : 0<C := laplaceGain_pos hj hjm hjn hjp zero_lt_one
  refine ⟨C/2,by positivity,fun t ht ht2 => ?_⟩
  have ht0 : 0<t := by linarith
  let q := m.dilate t ht0
  let g := physicalDilation f t ht0
  let jt (x : ℝ) := t*j (t*x)
  have hjt : Integrable jt := ((integrable_comp_mul_left_iff j ht0.ne').mpr hj).const_mul t
  have hjtm : Measurable jt := measurable_const.mul (hjm.comp (measurable_const.mul measurable_id))
  have hqmp : Measure.QuasiMeasurePreserving (fun x : ℝ => t*x) volume volume :=
    Measure.quasiMeasurePreserving_smul volume ht0.ne'
  have hsource : (fun x => sqrt (q.value x)*g x)=ᵐ[volume] jt := by
    filter_upwards [physicalDilation_coe f ht0,hqmp.ae hje] with x hx hjx
    change sqrt (t*m.value (t*x))*physicalDilation f t ht0 x=t*j (t*x)
    rw [hx,Real.sqrt_mul ht0.le]
    calc
      _ = (sqrt t)^2*(sqrt (m.value (t*x))*f (t*x)) := by ring
      _ = _ := by rw [Real.sq_sqrt ht0.le,hjx]
  have hbound := (kernelSpectralData q.integrable q.nonneg).top_quadratic_bound g
  rw [kernel_laplace_pairing q g hjt hjtm hsource,physicalDilation_norm,hf,one_pow,mul_one] at hbound
  change laplacePair jt 1 1≤observe q .top at hbound
  have hgain := laplace_dilation_lower hj hjm hjn (a := 1) (by norm_num) ht0
  rw [hpair] at hgain
  have hscaled : laplacePair jt 1 1=laplacePair j 1 t := laplacePair_scale j 1 ht0
  rw [hscaled] at hbound
  have hcoef : (t-1)/2≤1-1/t := by
    apply (mul_le_mul_iff_of_pos_right ht0).mp
    have hid : (1/t)*t=1 := div_mul_cancel₀ _ ht0.ne'
    nlinarith [mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr ht2)]
  have hb := mul_le_mul_of_nonneg_right hcoef hC.le
  change observe m .top+C/2*(t-1)≤observe q .top
  dsimp only [C] at *
  nlinarith

end
end jacobi.Variational
