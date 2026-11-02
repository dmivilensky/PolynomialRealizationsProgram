import jacobi.Analytic.L2Compression
import jacobi.Analytic.GLBaseInverse

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
The original real GL quadratic form is transferred to the actual complex
prefix Hilbert spaces. Its two real components use the same proved
constant kappa_star. No complex spectral-gap premise is introduced.
Use: transfers the original proved coercivity constant without changing its normalization.
-/
namespace jacobi.Analytic
noncomputable section
open Set MeasureTheory Filter jacobi.Reference jacobi.GelfandLevitan
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace
attribute [local irreducible] jacobi.GelfandLevitan.kernel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The true complex kernel form at real order is the sum of its original real and imaginary kernel forms.
Use: transfers the original proved coercivity constant without changing its normalization.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the actual double integral is integrable. Commute real part with this integral and use the two quotient-compatible component representatives on both product coordinates; the pointwise real identity is elementary complex multiplication. -/
theorem complexKernel_real_quadratic (a : ℝ) (ha : -1<a) (v : ComplexL2) :
    (inner ℂ v (complexKernelOperator (continuousOfReal (realKernelMap a ha)) v)).re=
      kernelQuadratic a ha (realL2 v)+kernelQuadratic a ha (imagL2 v) := by
  -- Product-coordinate almost-everywhere transport avoids pointwise assumptions on L2 representatives.
  let F := continuousOfReal (realKernelMap a ha)
  rw [complexKernelOperator_inner]
  have hre := integral_re (complexKernelBilinear_integrable F v v)
  change (∫ p:Interval×Interval,((star (v p.1)*v p.2)*F (halfClamp p.1,halfClamp p.2)).re
    ∂(volume.prod volume))=(∫ p:Interval×Interval,
      (star (v p.1)*v p.2)*F (halfClamp p.1,halfClamp p.2) ∂(volume.prod volume)).re at hre
  rw [← hre]
  unfold kernelQuadratic
  rw [← integral_add (kernelQuadratic_integrable a ha (realL2 v))
    (kernelQuadratic_integrable a ha (imagL2 v))]
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae_eq_comp (realL2_ae v),
    Measure.quasiMeasurePreserving_snd.ae_eq_comp (realL2_ae v),
    Measure.quasiMeasurePreserving_fst.ae_eq_comp (imagL2_ae v),
    Measure.quasiMeasurePreserving_snd.ae_eq_comp (imagL2_ae v)] with p hr1 hr2 hi1 hi2
  change ((star (v p.1)*v p.2)*(kernel a ha (halfTime p.1) (halfTime p.2):ℂ)).re=_
  dsimp only [Function.comp_def] at hr1 hr2 hi1 hi2
  rw [hr1,hr2,hi1,hi2]
  simp only [_root_.Complex.mul_re,_root_.Complex.mul_im,_root_.Complex.star_def,
    _root_.Complex.conj_re,_root_.Complex.conj_im,_root_.Complex.ofReal_re,_root_.Complex.ofReal_im,
    mul_zero,sub_zero,neg_mul,sub_neg_eq_add]
  ring

/-- The genuine complex GL real quadratic form at real order splits into the two original real GL forms.
Use: applies one actual kappa_star to every complex prefix input on every physical interval.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the interval projection preserves inner products with actual prefix vectors. Split the identity term by the exact complex L2 norm decomposition and use the proved original kernel-form identity. -/
theorem complexPrefix_real_quadratic (a : ℝ) (ha : -1<a) (t : ℝ) (v : complexPrefix t) :
    (inner ℂ v (complexPrefixPositive (continuousOfReal (realKernelMap a ha)) t v)).re=
      quadratic a ha (realL2 (v:ComplexL2))+quadratic a ha (imagL2 (v:ComplexL2)) := by
  -- Compression does not change the form on the genuine physical support subspace.
  have hp : inner ℂ v (complexPrefixPositive (continuousOfReal (realKernelMap a ha)) t v)=
      inner ℂ (v:ComplexL2) (v:ComplexL2)+
        inner ℂ (v:ComplexL2) (complexKernelOperator (continuousOfReal (realKernelMap a ha)) (v:ComplexL2)) := by
    change inner ℂ v (v+(complexPrefix t).orthogonalProjectionOnto _)=_
    rw [inner_add_right,(complexPrefix t).inner_orthogonalProjectionOnto_eq_of_mem_left]
    rfl
  have hn := InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (v:ComplexL2)
  change ‖(v:ComplexL2)‖^2=(inner ℂ (v:ComplexL2) (v:ComplexL2)).re at hn
  rw [hp,_root_.Complex.add_re,← hn,complexKernel_real_quadratic,complexL2_norm_sq]
  unfold quadratic
  ring

/-- The original real-base complex GL family has one strictly positive genuine coercivity constant on all physical intervals.
Use: supplies the source kappa_star for the unconditional complex inverse bound 2/kappa_star on one common order disk.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: use the already proved real all-interval coercivity. The real and imaginary parts of an actual complex prefix vector vanish on its same tail. Sum their two original bounds and apply the exact complex squared-norm decomposition. -/
theorem complexPrefix_real_coercive (a : ℝ) (ha : -1<a) :
    ∃ κ : ℝ,0<κ ∧
      (∀ t∈Ioc (0:ℝ) (1/2),∀ v:Space,
        (∀ᵐ s:Interval,t<(s:ℝ) → v s=0) → κ*‖v‖^2≤quadratic a ha v) ∧
      ∀ t∈Ioc (0:ℝ) (1/2),∀ v:complexPrefix t,
        κ*‖v‖^2≤(inner ℂ v (complexPrefixPositive (continuousOfReal (realKernelMap a ha)) t v)).re := by
  -- The common constant is obtained from the genuine original real theorem, not assumed for complex inputs.
  obtain ⟨κ,hκ,hq⟩ := quadratic_coercive_all_intervals a ha
  refine ⟨κ,hκ,hq,fun t ht v => ?_⟩
  have hs := (mem_complexPrefix t (v:ComplexL2)).mp v.property
  have hr : ∀ᵐ s:Interval,t<(s:ℝ) → realL2 (v:ComplexL2) s=0 := by
    filter_upwards [hs,realL2_ae (v:ComplexL2)] with s hs hr
    intro hst
    rw [hr,hs hst]
    rfl
  have hi : ∀ᵐ s:Interval,t<(s:ℝ) → imagL2 (v:ComplexL2) s=0 := by
    filter_upwards [hs,imagL2_ae (v:ComplexL2)] with s hs hi
    intro hst
    rw [hi,hs hst]
    rfl
  rw [complexPrefix_real_quadratic]
  have hn := complexL2_norm_sq (v:ComplexL2)
  change ‖v‖^2=_ at hn
  rw [hn,mul_add]
  exact add_le_add (hq t ht _ hr) (hq t ht _ hi)

end
end jacobi.Analytic
