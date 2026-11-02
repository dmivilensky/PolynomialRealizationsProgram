import jacobi.Analytic.ContinuousMapHolomorphy
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
Article: jacobi, Lemma C.1.
A singular positive-base power integral is holomorphic in its exponent.
On each parameter neighborhood, put the fixed integrable endpoint power
into the measure. The remaining positive-real-part power is holomorphic
in the continuous-function norm, including its zero spatial endpoints.
Source: holomorphic parameter integration by a fixed finite measure.
Use: removes the original beta-integral singularity by absorbing a fixed smaller power into its measure.
-/
namespace jacobi.Analytic
noncomputable section
open _root_.Complex Set Filter MeasureTheory
open scoped Topology ENNReal
variable {X:Type*} [TopologicalSpace X] [CompactSpace X]
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The genuine continuous complex power of a nonnegative compact-domain base at a positive-real-part exponent.
Use: removes the original beta-integral singularity by absorbing a fixed smaller power into its measure.
Article: jacobi, Lemma C.1.
-/
def positivePowerMap (B:C(X,ℝ)) (hB:∀ x,0≤B x) (g:ℂ) : C(X,ℂ) := by
  classical
  exact if hg:0<g.re then ⟨fun x => (B x:ℂ)^g,continuous_iff_continuousAt.mpr (fun x =>
    (Complex.continuousAt_cpow_of_re_pos (p := ((B x:ℂ),g))
      (Or.inl (by simpa only [Complex.ofReal_re] using hB x)) hg).comp_of_eq
        (f := fun y:X => ((B y:ℂ),g)) (by fun_prop) rfl)⟩ else 0

omit [CompactSpace X] in
/-- The compact-domain power family evaluates to the literal original complex power on its domain.
Use: identifies weighted-measure integrals with the original singular integrand.
Article: jacobi, Lemma C.1.
Proof: select the genuine positive-real-part branch. -/
theorem positivePowerMap_apply (B:C(X,ℝ)) (hB:∀ x,0≤B x) {g:ℂ} (hg:0<g.re) (x:X) :
    positivePowerMap B hB g x=(B x:ℂ)^g := by
  simp only [positivePowerMap,dite_eq_left hg,ContinuousMap.coe_mk]

/-- The actual nonnegative-base power family is holomorphic in the continuous-function norm throughout the positive-real-part exponent half-plane.
Use: proves holomorphy of the original singular reference integral after its fixed endpoint weight is put into the measure.
Article: jacobi, Lemma C.1.
Proof: community joint power continuity gives norm continuity on the compact spatial domain. At a nonzero base each evaluation is its genuine exponential formula; at a zero base it is identically zero on the domain. Apply the proved continuous-function-valued Cauchy theorem. -/
theorem positivePowerMap_holomorphic (B:C(X,ℝ)) (hB:∀ x,0≤B x) :
    DifferentiableOn ℂ (positivePowerMap B hB) {g | 0<g.re} := by
  -- Zero spatial bases stay in the true continuous-function family; they are not removed from the compact domain.
  have hU : IsOpen {g:ℂ | 0<g.re} := isOpen_lt continuous_const Complex.continuous_re
  have hc : ContinuousOn (positivePowerMap B hB) {g | 0<g.re} := by
    apply ContinuousMap.continuousOn_of_continuousOn_uncurry
    intro p hp
    have hpow := (Complex.continuousAt_cpow_of_re_pos (p := ((B p.2:ℂ),p.1))
      (Or.inl (by simpa only [Complex.ofReal_re] using hB p.2)) hp.1).comp_of_eq
        (f := fun q:ℂ × X => ((B q.2:ℂ),q.1)) (by fun_prop) rfl
    apply hpow.continuousWithinAt.congr_of_eventuallyEq_of_mem ?_ hp
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact positivePowerMap_apply B hB hq.1 q.2
  apply continuousMap_differentiableOn hU hc
  intro x g hg
  by_cases hx : B x=0
  · apply (differentiableWithinAt_const (0:ℂ)).congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin] with h hh
      rw [positivePowerMap_apply B hB hh x,hx,Complex.ofReal_zero,Complex.zero_cpow (ne_of_apply_ne Complex.re hh.ne')]
    · rw [positivePowerMap_apply B hB hg x,hx,Complex.ofReal_zero,Complex.zero_cpow (ne_of_apply_ne Complex.re hg.ne')]
  · have he : DifferentiableAt ℂ (fun g:ℂ => Complex.exp (Complex.log (B x:ℂ)*g)) g := by fun_prop
    apply he.differentiableWithinAt.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin] with h hh
      rw [positivePowerMap_apply B hB hh x,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx)]
    · rw [positivePowerMap_apply B hB hg x,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx)]

/-- The original singular power integral is genuinely convergent and holomorphic in its exponent throughout Re(g)>0.
Use: proves convergence and holomorphy of the actual beta/sine defining integral at complex order, independently of its Gauss representation.
Article: jacobi, Lemma C.1.
Proof: at the chosen exponent take epsilon equal to half its positive real part. Its actual integrable power B^(epsilon-1) defines a finite weighted measure. The remaining B^(g-epsilon) is holomorphic in the compact-domain function norm. Its fixed-measure integral is therefore holomorphic; almost-everywhere positive bases and the exact complex power addition law identify it with the original singular integral. -/
theorem positive_power_integral_holomorphic [MeasurableSpace X] [BorelSpace X]
    (μ:Measure X) (B:C(X,ℝ)) (hB:∀ x,0≤B x) (hpos:∀ᵐ x∂μ,0<B x)
    (hw:∀ ε:ℝ,0<ε → Integrable (fun x => B x^(ε-1)) μ) (H:C(X,ℂ))
    {g:ℂ} (hg:0<g.re) :
    Integrable (fun x => (B x:ℂ)^(g-1)*H x) μ ∧
      DifferentiableAt ℂ (fun z:ℂ => ∫ x,(B x:ℂ)^(z-1)*H x ∂μ) g := by
  -- The measure, not the analytic function, carries the fixed singular endpoint power.
  let ε : ℝ := g.re/2
  have hε : 0<ε := half_pos hg
  let w : X→ℝ := fun x => B x^(ε-1)
  have hw0 : ∀ x,0≤w x := fun x => Real.rpow_nonneg (hB x) _
  have hwi : Integrable w μ := hw ε hε
  have hwm : Measurable w := B.continuous.measurable.pow_const _
  let ν : Measure X := μ.withDensity (fun x => ENNReal.ofReal (w x))
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity
    ((lintegral_ofReal_ne_top_iff_integrable hwi.aestronglyMeasurable
      (Eventually.of_forall hw0)).mpr hwi)
  let L : C(X,ℂ) →L[ℂ] ℂ := L1.integralCLM' ℂ ∘L ContinuousMap.toLp (𝕜 := ℂ) (p := 1) ν
  have hL (f:C(X,ℂ)) : L f=∫ x,f x ∂ν := by
    change L1.integralCLM' ℂ (ContinuousMap.toLp (𝕜 := ℂ) (p := 1) ν f)=_
    rw [← L1.integral_eq' ℂ,L1.integral_eq_integral]
    exact integral_congr_ae (ContinuousMap.coeFn_toLp ν f)
  have heq {z:ℂ} (hz:ε<z.re) :
      L (positivePowerMap B hB (z-ε)*H)=∫ x,(B x:ℂ)^(z-1)*H x ∂μ := by
    rw [hL,integral_withDensity_eq_integral_toReal_smul (hwm.ennreal_ofReal)
      (Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
    apply integral_congr_ae
    filter_upwards [hpos] with x hx
    rw [ENNReal.toReal_ofReal (hw0 x)]
    change (w x:ℂ)*(positivePowerMap B hB (z-ε) x*H x)=_
    rw [positivePowerMap_apply B hB (by simp only [Complex.sub_re,Complex.ofReal_re]; linarith) x]
    have hwc : (w x:ℂ)=(B x:ℂ)^((ε-1:ℝ):ℂ) := Complex.ofReal_cpow hx.le _
    rw [hwc,← mul_assoc,← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')]
    congr 2
    push_cast
    ring
  have hzg : 0<(g-(ε:ℂ)).re := by simp only [Complex.sub_re,Complex.ofReal_re]; dsimp [ε]; linarith
  have hmap := positivePowerMap_holomorphic B hB
  have hmapAt := hmap.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hzg)
  have hs := (hmapAt.comp g (differentiableAt_id.sub_const (ε:ℂ))).mul_const H
  have hd := L.differentiableAt.comp g hs
  have hevent : (fun z:ℂ => ∫ x,(B x:ℂ)^(z-1)*H x ∂μ)=ᶠ[𝓝 g]
      (fun z => L (positivePowerMap B hB (z-ε)*H)) := by
    filter_upwards [Complex.continuous_re.continuousAt.eventually_const_lt
      (by dsimp [ε]; linarith : ε<g.re)] with z hz
    exact (heq hz).symm
  refine ⟨?_,hd.congr_of_eventuallyEq hevent⟩
  have hi := ((positivePowerMap B hB (g-ε)*H).memLp ℂ (p := 1) (μ := ν)).integrable (by simp)
  have hi' := (integrable_withDensity_iff_integrable_smul' hwm.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mp hi
  apply hi'.congr
  filter_upwards [hpos] with x hx
  rw [ENNReal.toReal_ofReal (hw0 x)]
  change (w x:ℂ)*(positivePowerMap B hB (g-ε) x*H x)=_
  rw [positivePowerMap_apply B hB hzg x]
  have hwc : (w x:ℂ)=(B x:ℂ)^((ε-1:ℝ):ℂ) := Complex.ofReal_cpow hx.le _
  rw [hwc,← mul_assoc,← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')]
  congr 2
  push_cast
  ring

end
end jacobi.Analytic
