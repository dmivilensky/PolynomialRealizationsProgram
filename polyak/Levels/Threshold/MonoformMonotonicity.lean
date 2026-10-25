import polyak.Levels.Threshold.Monoform

/-! Monotone changes of an integrable profile preserve its actual measure. -/
noncomputable section
open MeasureTheory
namespace polyak.Levels.Threshold

theorem integrable_monotoneLag {h : Frequency→ℝ} {ν : Measure Frequency}
    [IsFiniteMeasure ν] (hh : Integrable h ν) (n : ℤ) : Integrable (monotoneLag h n) ν := by
  have hc : AEStronglyMeasurable (fun ω:Frequency => 1-Real.cos ((n:ℝ)*(ω:ℝ))) ν :=
    (show Continuous (fun ω:Frequency => 1-Real.cos ((n:ℝ)*(ω:ℝ))) by fun_prop).aestronglyMeasurable
  have hb : ∀ᵐω : Frequency ∂ν,‖1-Real.cos ((n:ℝ)*(ω:ℝ))‖≤2 := by
    filter_upwards with ω
    rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one _))]
    linarith [Real.neg_one_le_cos ((n:ℝ)*(ω:ℝ))]
  exact (hh.mul_bdd hc hb).sub
    ((show Continuous (fun ω:Frequency => Real.sin ((n:ℝ)*(ω:ℝ))) by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))

theorem MonotoneSolution.mono_ae {h h' : Frequency→ℝ} {ν : Measure Frequency}
    (hν : MonotoneSolution h ν) (hm' : AEStronglyMeasurable h' ν)
    (horder : ∀ᵐω∂ν,h ω≤h' ω) {H : ℝ} (hupper : ∀ᵐω∂ν,h' ω≤H) :
    MonotoneSolution h' ν ∧ ∀n:ℤ,
      (∫ ω,monotoneLag h' n ω ∂ν)=(∫ ω,monotoneLag h n ω ∂ν)+
        ∫ ω,(h' ω-h ω)*(1-Real.cos ((n:ℝ)*(ω:ℝ))) ∂ν := by
  have : IsFiniteMeasure ν := hν.1
  have hh := hν.2.2.2.1
  have hh' : Integrable h' ν :=
    (hh.abs.add (integrable_const |H|)).mono' hm' (by
      filter_upwards [horder,hupper] with ω ho hu
      rw [Real.norm_eq_abs]
      change |h' ω|≤|h ω|+|H|
      apply abs_le.mpr
      constructor <;> linarith [le_abs_self (h ω),neg_abs_le (h ω),le_abs_self H,abs_nonneg (h ω),abs_nonneg H])
  have hid (n:ℤ) : monotoneLag h' n=fun ω => monotoneLag h n ω+
      (h' ω-h ω)*(1-Real.cos ((n:ℝ)*(ω:ℝ))) := by funext ω; dsimp [monotoneLag]; ring
  have hdiff (n:ℤ) : Integrable (fun ω => (h' ω-h ω)*(1-Real.cos ((n:ℝ)*(ω:ℝ)))) ν := by
    have he : (fun ω => (h' ω-h ω)*(1-Real.cos ((n:ℝ)*(ω:ℝ))))=
        fun ω => monotoneLag h' n ω-monotoneLag h n ω := by funext ω; dsimp [monotoneLag]; ring
    rw [he]
    exact (integrable_monotoneLag hh' n).sub (integrable_monotoneLag hh n)
  have hi (n:ℤ) : (∫ ω,monotoneLag h' n ω ∂ν)=(∫ ω,monotoneLag h n ω ∂ν)+
      ∫ ω,(h' ω-h ω)*(1-Real.cos ((n:ℝ)*(ω:ℝ))) ∂ν := by
    rw [hid,integral_add (integrable_monotoneLag hh n) (hdiff n)]
  refine ⟨⟨hν.1,hν.2.1,hν.2.2.1,hh',?_,fun n hn => ?_⟩,hi⟩
  · exact hν.2.2.2.2.1.trans (integral_mono_ae hh hh' horder)
  · rw [hi]
    exact add_nonneg (hν.2.2.2.2.2 n hn) (integral_nonneg_of_ae
      (horder.mono fun ω hω => mul_nonneg (sub_nonneg.mpr hω) (sub_nonneg.mpr (Real.cos_le_one _))))

theorem MonotoneSolution.mono_on_support_aestronglyMeasurable {h h' : Frequency→ℝ} {ν : Measure Frequency}
    (hν : MonotoneSolution h ν) (hm' : AEStronglyMeasurable h' ν)
    (horder : ∀ω∈ν.support,h ω≤h' ω) {H : ℝ} (hupper : ∀ω∈ν.support,h' ω≤H) :
    MonotoneSolution h' ν ∧ ∀n:ℤ,
      (∫ ω,monotoneLag h' n ω ∂ν)=(∫ ω,monotoneLag h n ω ∂ν)+
        ∫ ω,(h' ω-h ω)*(1-Real.cos ((n:ℝ)*(ω:ℝ))) ∂ν := by
  have hs : ∀ᵐω∂ν,ω∈ν.support := ν.support_mem_ae
  exact hν.mono_ae hm'
    (hs.mono fun ω hω => horder ω hω) (hs.mono fun ω hω => hupper ω hω)

theorem MonotoneSolution.mono_on_support {h h' : Frequency→ℝ} {ν : Measure Frequency}
    (hν : MonotoneSolution h ν) (hm' : Measurable h')
    (horder : ∀ω∈ν.support,h ω≤h' ω) {H : ℝ} (hupper : ∀ω∈ν.support,h' ω≤H) :
    MonotoneSolution h' ν ∧ ∀n:ℤ,
      (∫ ω,monotoneLag h' n ω ∂ν)=(∫ ω,monotoneLag h n ω ∂ν)+
        ∫ ω,(h' ω-h ω)*(1-Real.cos ((n:ℝ)*(ω:ℝ))) ∂ν :=
  hν.mono_on_support_aestronglyMeasurable hm'.aestronglyMeasurable horder hupper

end polyak.Levels.Threshold
