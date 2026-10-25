import polyak.Levels.Program.Alternative
import polyak.Levels.Program.Carried
import polyak.Levels.Geometry.ShiftedCurve
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! Closedness under simultaneous curve and arbitrary-measure variation. -/
noncomputable section
open MeasureTheory
open scoped Topology
namespace polyak.Levels.Threshold

theorem continuous_angle_integral_family {X : Type*} [TopologicalSpace X]
    {ν : X→ProbabilityMeasure Frequency} {f : X→C(Frequency,ℝ)}
    (hν : Continuous ν) (hf : Continuous f) :
    Continuous (fun x => ∫ω,f x ω ∂ν x) := by
  apply continuous_iff_continuousAt.mpr
  intro x₀
  have herror : Filter.Tendsto (fun x => ∫ω,(f x-f x₀) ω ∂ν x) (𝓝 x₀) (𝓝 0) := by
    apply squeeze_zero_norm
    · intro x
      have hb := norm_integral_le_of_norm_le_const (μ:=(ν x:Measure Frequency))
        (Filter.Eventually.of_forall fun ω => (f x-f x₀).norm_coe_le_norm ω)
      simpa using hb
    · have hn : Continuous (fun x => ‖f x-f x₀‖) := (hf.sub continuous_const).norm
      simpa using hn.tendsto x₀
  have hfixed := ((ProbabilityMeasure.continuous_integral_continuousMap (f x₀)).comp hν).tendsto x₀
  have hsum := herror.add hfixed
  simp only [zero_add] at hsum
  change Filter.Tendsto (fun x => ∫ω,f x ω ∂ν x) (𝓝 x₀) (𝓝 (∫ω,f x₀ ω ∂ν x₀))
  convert hsum using 1
  · funext x
    dsimp only [Function.comp_apply]
    rw [← integral_add]
    · congr 1
      funext ω
      simp
    · exact (f x-f x₀).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    · exact (f x₀).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · rfl

theorem isClosed_probabilitySolution_family {X : Type*} [TopologicalSpace X]
    (Θ : X→Curve) (hc : Continuous (fun p:X×Frequency => Θ p.1 p.2)) (𝒩 : Set ℤ) :
    IsClosed {p : X×ProbabilityMeasure Frequency | ProbabilitySolution (Θ p.1) 𝒩 p.2} := by
  let f : X→C(Frequency,ℝ) := fun x => ⟨(Θ x).minimizer,(Θ x).continuous_minimizer⟩
  have hf : Continuous f := ContinuousMap.continuous_of_continuous_uncurry f
    (Real.continuous_cos.comp hc)
  have hG : IsClosed {p : X×ProbabilityMeasure Frequency | 0 ≤ (∫ ω,(Θ p.1).minimizer ω ∂p.2)} :=
    isClosed_le continuous_const (continuous_angle_integral_family continuous_snd (hf.comp continuous_fst))
  have hL : IsClosed {p : X×ProbabilityMeasure Frequency | ∀n∈𝒩,0≤(∫ω,(Θ p.1).lag n ω ∂p.2)} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro n
    apply isClosed_iInter
    intro _
    let g : X→C(Frequency,ℝ) := fun x => ⟨(Θ x).lag n,(Θ x).continuous_lag n⟩
    have hg : Continuous g := ContinuousMap.continuous_of_continuous_uncurry g
      ((Real.continuous_cos.comp hc).sub (Real.continuous_cos.comp
        ((continuous_const.mul (continuous_subtype_val.comp continuous_snd)).sub hc)))
    exact isClosed_le continuous_const (continuous_angle_integral_family continuous_snd (hg.comp continuous_fst))
  exact hG.inter hL

theorem isClosed_fpOn_family {X : Type*} [TopologicalSpace X]
    (Θ : X→Curve) (hc : Continuous (fun p:X×Frequency => Θ p.1 p.2)) (𝒩 : Set ℤ) :
    IsClosed {x | FPOn (Θ x) 𝒩} := by
  have hs := isClosedMap_fst_of_compactSpace _ (isClosed_probabilitySolution_family Θ hc 𝒩)
  have he : Prod.fst '' {p : X×ProbabilityMeasure Frequency | ProbabilitySolution (Θ p.1) 𝒩 p.2}=
      {x | FPOn (Θ x) 𝒩} := by
    ext x
    constructor
    · rintro ⟨p,hp,rfl⟩
      exact (fpOn_iff_probability _ _).mpr ⟨p.2,hp⟩
    · intro hx
      obtain ⟨ν,hν⟩ := (fpOn_iff_probability _ _).mp hx
      exact ⟨(x,ν),hν,rfl⟩
  rw [← he]
  exact hs

theorem isClosed_carriedProbability {A : Set Frequency} (hA : IsClosed A) (hane : A.Nonempty) :
    IsClosed {ν : ProbabilityMeasure Frequency | ∀ᵐω∂(ν:Measure Frequency),ω∈A} := by
  let f : C(Frequency,ℝ) := ⟨fun ω => Metric.infDist ω A,Metric.continuous_infDist_pt A⟩
  have hi (ν:ProbabilityMeasure Frequency) : Integrable f (ν:Measure Frequency) :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he (ν:ProbabilityMeasure Frequency) : (∀ᵐω∂(ν:Measure Frequency),ω∈A) ↔ (∫ω,f ω ∂ν)=0 := by
    rw [integral_eq_zero_iff_of_nonneg (fun ω => (show 0≤f ω from Metric.infDist_nonneg)) (hi ν)]
    constructor
    · intro h
      exact h.mono fun ω hω => (hA.mem_iff_infDist_zero hane).mp hω
    · intro h
      exact h.mono fun ω hω => (hA.mem_iff_infDist_zero hane).mpr hω
  have hset : {ν : ProbabilityMeasure Frequency | (∀ᵐω∂(ν:Measure Frequency),ω∈A)}=
      {ν : ProbabilityMeasure Frequency | (∫ω,f ω ∂ν)=0} := by ext ν; exact he ν
  rw [hset]
  exact isClosed_eq (ProbabilityMeasure.continuous_integral_continuousMap f) continuous_const

theorem isClosed_supported_family {X : Type*} [TopologicalSpace X]
    (Θ : X→Curve) (hc : Continuous (fun p:X×Frequency => Θ p.1 p.2)) (𝒩 : Set ℤ)
    {A : Set Frequency} (hA : IsClosed A) (hane : A.Nonempty) :
    IsClosed {x | ∃ν:ProbabilityMeasure Frequency,
      ProbabilitySolution (Θ x) 𝒩 ν ∧ ∀ᵐω∂(ν:Measure Frequency),ω∈A} := by
  have hr := (isClosed_probabilitySolution_family Θ hc 𝒩).inter
    ((isClosed_carriedProbability hA hane).preimage continuous_snd)
  have hs := isClosedMap_fst_of_compactSpace _ hr
  have he : Prod.fst '' {p : X×ProbabilityMeasure Frequency | ProbabilitySolution (Θ p.1) 𝒩 p.2 ∧
      (∀ᵐω∂(p.2:Measure Frequency),ω∈A)}=
      {x | ∃ν:ProbabilityMeasure Frequency,ProbabilitySolution (Θ x) 𝒩 ν ∧
        (∀ᵐω∂(ν:Measure Frequency),ω∈A)} := by
    ext x
    constructor
    · rintro ⟨p,⟨hp,hAν⟩,rfl⟩
      exact ⟨p.2,hp,hAν⟩
    · rintro ⟨ν,hν,hAν⟩
      exact ⟨(x,ν),⟨hν,hAν⟩,rfl⟩
  rw [← he]
  exact hs

theorem shiftedCurve_jointContinuous :
    Continuous (fun p:(General.Tuning×ℝ)×Frequency => Geometry.shiftedCurve p.1.1 p.1.2 p.2) := by
  change Continuous (fun p:(General.Tuning×ℝ)×Frequency => Geometry.shiftedAngle p.1.1 p.1.2 p.2)
  have hg : Continuous (fun p:(General.Tuning×ℝ)×Frequency => (p.1.1,p.1.2,p.2)) :=
    continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd)
  have ht := Geometry.shiftedAngle_jointContinuous.comp hg
  exact ht.congr (fun _ => rfl)

theorem isClosed_shifted_fpOn (𝒩 : Set ℤ) :
    IsClosed {p:General.Tuning×ℝ | FPOn (Geometry.shiftedCurve p.1 p.2) 𝒩} :=
  isClosed_fpOn_family (fun p:General.Tuning×ℝ => Geometry.shiftedCurve p.1 p.2) shiftedCurve_jointContinuous 𝒩

end polyak.Levels.Threshold
