import jacobi.Support.ContinuumVolterra
import Mathlib.MeasureTheory.Integral.Prod

/-!
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
The original single-integral reduction-of-order Cauchy kernel equals
the already proved nested ground operator. A genuine triangular Fubini
argument is valid through the singular corner: monotonicity of the
ground state bounds its normalized triangular integrand by a constant.
Use: states the source continuum Volterra equation with its original single spatial integral.
-/
namespace jacobi.Support
noncomputable section
open Real Set Complex Filter MeasureTheory jacobi.Reference
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The literal reduction-of-order Cauchy kernel, included in the complex scalar field.
Use: states the source continuum Volterra equation with its original single spatial integral.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
The constant ground amplitude cancels, so the genuine normalized sine-power weight is used. -/
def groundCauchyKernel (a t s:ℝ) : ℂ :=
  (weight a t:ℂ)*(weight a s:ℂ)*(∫ r in s..t,((weight a r:ℂ)^2)⁻¹)

/-- The original single-integral continuum Cauchy action.
Use: supplies exactly the operator G_c in the printed continuum Volterra lemma.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
-/
def groundCauchyAction (a:ℝ) (v:ℝ→ℂ) (t:ℝ) : ℂ :=
  ∫ s in (0:ℝ)..t,groundCauchyKernel a t s*v s

/-- The genuine ground-normalized triangular integrand used to interchange the original two integrals.
Use: integrable triangular Fubini proves the literal single-kernel representation.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
-/
def groundTriangle (a:ℝ) (q:ℝ→ℂ) (r s:ℝ) : ℂ :=
  if s≤r then (weight a s:ℂ)^2*q s/(weight a r:ℂ)^2 else 0

/-- The true triangular ground integrand is integrable through its actual singular corner for every continuous regular factor.
Use: justifies the genuine Fubini passage from nested primitives to the printed Cauchy kernel.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: the integrand is measurable. On the actual triangle the positive ground state is increasing, so its squared ratio is at most one. The continuous regular factor is bounded on the fixed compact half interval, giving an integrable constant majorant on the finite rectangle. -/
theorem groundTriangle_integrable {a:ℝ} (ha:-1<a) {q:ℝ→ℂ} (hq:Continuous q)
    {t:ℝ} (ht:t∈Icc (0:ℝ) (1/2)) :
    IntegrableOn (Function.uncurry (groundTriangle a q)) (uIoc (0:ℝ) t ×ˢ uIoc (0:ℝ) t) := by
  -- Only genuine positive interior coordinates are needed; their null boundary does not enter the estimate.
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (hq.continuousOn (s := Icc (0:ℝ) (1/2)))
  let M : ℝ := |B|+1
  have hM : 0≤M := by dsimp [M]; positivity
  have hw : Continuous (fun s:ℝ => (weight a s:ℂ)) := Complex.continuous_ofReal.comp (weight_properties ha).1
  have hm : Measurable (Function.uncurry (groundTriangle a q)) :=
    Measurable.ite (measurableSet_le measurable_snd measurable_fst)
      ((((hw.measurable.comp measurable_snd).pow_const 2).mul (hq.measurable.comp measurable_snd)).div
        ((hw.measurable.comp measurable_fst).pow_const 2)) measurable_const
  have hfinite : (volume:Measure (ℝ × ℝ)) (uIoc (0:ℝ) t ×ˢ uIoc (0:ℝ) t)<∞ := by
    rw [Measure.volume_eq_prod,Measure.prod_prod]
    simp only [Real.volume_Ioc,uIoc_of_le ht.1]
    finiteness
  apply IntegrableOn.of_bound hfinite hm.aestronglyMeasurable.restrict M
  filter_upwards [ae_restrict_mem (measurableSet_uIoc.prod measurableSet_uIoc)] with p hp
  rw [uIoc_of_le ht.1] at hp
  change ‖groundTriangle a q p.1 p.2‖≤M
  by_cases hsr : p.2≤p.1
  · have hr : 0<weight a p.1 := weight_pos a ⟨hp.1.1,by linarith [hp.1.2,ht.2]⟩
    have hs : 0<weight a p.2 := weight_pos a ⟨hp.2.1,by linarith [hp.2.2,ht.2]⟩
    have hmono := groundWeight_monotone ha ⟨hp.2.1.le,hp.2.2.trans ht.2⟩
      ⟨hp.1.1.le,hp.1.2.trans ht.2⟩ hsr
    have hqM : ‖q p.2‖≤M := (hB _ ⟨hp.2.1.le,hp.2.2.trans ht.2⟩).trans
      (by dsimp [M]; linarith [le_abs_self B])
    simp only [groundTriangle,ite_eq_left hsr,norm_div,norm_mul,norm_pow,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos hs,abs_of_pos hr]
    apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
    exact (mul_le_mul_of_nonneg_left hqM (sq_nonneg _)).trans
      (by nlinarith [mul_le_mul_of_nonneg_right ((sq_le_sq₀ hs.le hr.le).mpr hmono) hM])
  · simp only [groundTriangle,ite_eq_right hsr,norm_zero]
    exact hM

/-- Integrating the true triangle along its inner source coordinate gives precisely the existing ground flux.
Use: identifies one side of the genuine triangular Fubini equality with the original nested Volterra operator.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: the triangular indicator restricts the actual fixed outer interval to [0,r]. Its genuine inner integral is exactly the original weighted primitive divided by the endpoint ground square. -/
theorem groundTriangle_source (a:ℝ) (q:ℝ→ℂ) {t r:ℝ} (ht:0≤t) (hr:r∈Icc 0 t) :
    (∫ s in (0:ℝ)..t,groundTriangle a q r s)=groundFlux a q r := by
  -- The interval restriction is an exact measurable indicator identity.
  rw [intervalIntegral.integral_of_le ht]
  change (∫ s in Ioc (0:ℝ) t,(Iic r).indicator
    (fun s => (weight a s:ℂ)^2*q s/(weight a r:ℂ)^2) s)=_
  rw [setIntegral_indicator measurableSet_Iic,Ioc_inter_Iic,min_eq_right hr.2,
    ← intervalIntegral.integral_of_le hr.1,intervalIntegral.integral_div]
  rfl

/-- Integrating the true triangle along its other coordinate gives the original reduction-of-order primitive.
Use: identifies the other side of Fubini with the printed Cauchy kernel rather than a stipulated operator.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: the triangular indicator restricts the actual interval to [s,t]; null endpoints identify its set and interval integrals. Pull out the genuine constant source factor. -/
theorem groundTriangle_target (a:ℝ) (q:ℝ→ℂ) {t s:ℝ} (ht:0≤t) (hs:s∈Ioc 0 t) :
    (∫ r in (0:ℝ)..t,groundTriangle a q r s)=
      (weight a s:ℂ)^2*q s*(∫ r in s..t,((weight a r:ℂ)^2)⁻¹) := by
  -- The strict positive source coordinate makes the lower boundary change harmless and explicit.
  rw [intervalIntegral.integral_of_le ht]
  change (∫ r in Ioc (0:ℝ) t,(Ici s).indicator
    (fun r => (weight a s:ℂ)^2*q s/(weight a r:ℂ)^2) r)=_
  have he : Ioc (0:ℝ) t ∩ Ici s=Icc s t := by
    ext r
    constructor
    · intro hr; exact ⟨hr.2,hr.1.2⟩
    · intro hr; exact ⟨⟨hs.1.trans_le hr.1,hr.2⟩,hr.1⟩
  rw [setIntegral_indicator measurableSet_Ici,he,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hs.2]
  simp only [div_eq_mul_inv]
  exact intervalIntegral.integral_const_mul _ _

/-- The literal original single-integral Cauchy action equals the actual nested ground Volterra operator.
Use: translates the proved original solution and uniqueness into the exact printed continuum Volterra equation.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: the actual triangular normalized integrand is genuinely integrable. Interchange its two ordinary interval integrals, identify their exact source and target values and factor out the unchanged ground value. -/
theorem groundCauchyAction_nested {a:ℝ} (ha:-1<a) {q:ℝ→ℂ} (hq:Continuous q)
    {t:ℝ} (ht:t∈Icc (0:ℝ) (1/2)) :
    groundCauchyAction a (fun s => (weight a s:ℂ)*q s) t=(weight a t:ℂ)*groundVolterra a q t := by
  -- Fubini is applied only after the true singular-corner integrability is proved.
  have he := intervalIntegral_intervalIntegral_swap (groundTriangle_integrable ha hq ht)
  have hleft : (∫ r in (0:ℝ)..t,∫ s in (0:ℝ)..t,groundTriangle a q r s)=groundVolterra a q t := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le ht.1] at hr
    exact groundTriangle_source a q ht.1 hr
  rw [hleft] at he
  rw [he,groundCauchyAction,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_ae
  filter_upwards with s hs
  have hs' : s∈Ioc (0:ℝ) t := by simpa only [uIoc_of_le ht.1] using hs
  rw [groundTriangle_target a q ht.1 hs']
  unfold groundCauchyKernel
  ring

end
end jacobi.Support
