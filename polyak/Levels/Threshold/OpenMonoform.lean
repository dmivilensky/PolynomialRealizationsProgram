import polyak.Levels.Threshold.Monoform

/-! Literal open-interval measures are equivalent to the carried closed-interval
representation. Both directions use actual push-forwards and pull-backs. -/
noncomputable section
open MeasureTheory
namespace polyak.Levels.Threshold

abbrev OpenFrequency := interiorCarrier

def OpenMonotoneSolution (h : OpenFrequency→ℝ) (ν : Measure OpenFrequency) : Prop :=
  IsFiniteMeasure ν ∧ ν≠0 ∧ Integrable h ν ∧ 0≤∫ω,h ω ∂ν ∧
    ∀n:ℤ,n≠0→0≤∫ω,h ω*(1-Real.cos ((n:ℝ)*(ω.val:ℝ)))-Real.sin ((n:ℝ)*(ω.val:ℝ)) ∂ν

theorem monotoneSolution_map_iff (h : Frequency→ℝ) (μ : Measure OpenFrequency) :
    MonotoneSolution h (μ.map (Subtype.val:OpenFrequency→Frequency)) ↔
      OpenMonotoneSolution (fun ω=>h ω.val) μ := by
  let f : OpenFrequency→Frequency := Subtype.val
  have hf : MeasurableEmbedding f := MeasurableEmbedding.subtype_coe measurableSet_interiorCarrier
  have hi : Integrable h (μ.map f) ↔ Integrable (fun ω=>h ω.val) μ := hf.integrable_map_iff
  have hG : (∫ω,h ω ∂μ.map f)=∫ω:OpenFrequency,h ω.val ∂μ := hf.integral_map h
  have hL (n:ℤ) : (∫ω,monotoneLag h n ω ∂μ.map f)=
      ∫ω:OpenFrequency,h ω.val*(1-Real.cos ((n:ℝ)*(ω.val:ℝ)))-Real.sin ((n:ℝ)*(ω.val:ℝ)) ∂μ :=
    hf.integral_map (monotoneLag h n)
  dsimp only [f] at hi hG hL
  constructor
  · rintro ⟨hfinite,hne,_,hhi,hmin,hlag⟩
    have : IsFiniteMeasure (μ.map f) := hfinite
    have hfinite' : IsFiniteMeasure μ := by rw [← hf.comap_map μ]; infer_instance
    exact ⟨hfinite',(Measure.map_ne_zero_iff hf.measurable.aemeasurable).mp hne,
      hi.mp hhi,by simpa only [hG] using hmin,fun n hn=>by simpa only [hL n] using hlag n hn⟩
  · rintro ⟨hfinite,hne,hhi,hmin,hlag⟩
    have : IsFiniteMeasure μ := hfinite
    have hcar : ∀ᵐω∂μ.map f,ω∈interiorCarrier := hf.ae_map_iff.mpr
      (Filter.Eventually.of_forall (fun ω=>ω.property))
    exact ⟨inferInstance,(Measure.map_ne_zero_iff hf.measurable.aemeasurable).mpr hne,
      hcar,hi.mpr hhi,by simpa only [hG] using hmin,fun n hn=>by simpa only [hL n] using hlag n hn⟩

theorem exists_monotoneSolution_iff_open (h : Frequency→ℝ) :
    (∃ν : Measure Frequency,MonotoneSolution h ν) ↔
      ∃μ : Measure OpenFrequency,OpenMonotoneSolution (fun ω=>h ω.val) μ := by
  constructor
  · rintro ⟨ν,hν⟩
    let μ := ν.comap (Subtype.val:OpenFrequency→Frequency)
    have hmap : μ.map (Subtype.val:OpenFrequency→Frequency)=ν := by
      rw [map_comap_subtype_coe measurableSet_interiorCarrier,Measure.restrict_eq_self_of_ae_mem hν.2.2.1]
    exact ⟨μ,(monotoneSolution_map_iff h μ).mp (by rw [hmap]; exact hν)⟩
  · rintro ⟨μ,hμ⟩
    exact ⟨μ.map Subtype.val,(monotoneSolution_map_iff h μ).mpr hμ⟩

theorem shifted_open_monoform_iff (q : General.Tuning) (s : ℝ) :
    FP (Geometry.shiftedCurve q s) ↔
      ∃μ : Measure OpenFrequency,OpenMonotoneSolution (fun ω=>shiftedCotangent q s ω.val) μ :=
  (shifted_monoform_iff q s).trans (exists_monotoneSolution_iff_open _)

end polyak.Levels.Threshold
