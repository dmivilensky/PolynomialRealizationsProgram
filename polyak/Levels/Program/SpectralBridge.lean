import polyak.Levels.Program.SourceMoments

/-! Exact equivalence with the original cosine-coordinate spectral feasibility at t=0. -/
noncomputable section
open MeasureTheory
namespace polyak.Levels

theorem spectrumG_coordinates (q : General.Tuning) (ν : ProbabilityMeasure Frequency) :
    Waves.spectrumG (Spectral.spectrumCoordinates ν) (Waves.multiplierMap q.A q.B q.beta 0)=
      ∫ ω,sourceG q ω ∂ν := by
  change Spectral.avg (Spectral.spectrumCoordinates ν)
    (fun c => 1-Complex.normSq (Waves.multiplierMap q.A q.B q.beta 0 c))=_
  rw [Spectral.avg_spectrumCoordinates ν (by fun_prop)]
  rfl

theorem spectrumA_coordinates (q : General.Tuning) (ν : ProbabilityMeasure Frequency) (n : ℕ) :
    Waves.spectrumA (Spectral.spectrumCoordinates ν) (Waves.multiplierMap q.A q.B q.beta 0) 0 n=
      ∫ ω,sourceG q ω*(1-Real.cos ((n:ℝ)*(ω:ℝ))) ∂ν := by
  change Spectral.avg (Spectral.spectrumCoordinates ν)
    (fun c => (1-Complex.normSq (Waves.multiplierMap q.A q.B q.beta 0 c))*
      (Real.cosh ((n:ℝ)*0)-Real.cos ((n:ℝ)*Real.arccos c)))=_
  rw [Spectral.avg_spectrumCoordinates ν (by fun_prop)]
  apply integral_congr_ae
  filter_upwards with ω
  change (1-Complex.normSq (Waves.multiplierMap q.A q.B q.beta 0 (Spectral.cosineCoordinates ω)))*
    (Real.cosh ((n:ℝ)*0)-Real.cos ((n:ℝ)*Real.arccos (Real.cos (ω:ℝ))))=_
  rw [Real.arccos_cos ω.property.1 ω.property.2]
  simp only [mul_zero,Real.cosh_zero]
  rfl

theorem spectrumB_coordinates (q : General.Tuning) (ν : ProbabilityMeasure Frequency) (n : ℕ) :
    Waves.spectrumB (Spectral.spectrumCoordinates ν) (Waves.multiplierMap q.A q.B q.beta 0) n=
      ∫ ω,2*(angleMultiplier q ω).im*Real.sin ((n:ℝ)*(ω:ℝ)) ∂ν := by
  change Spectral.avg (Spectral.spectrumCoordinates ν)
    (fun c => 2*(Waves.multiplierMap q.A q.B q.beta 0 c).im*
      Real.sin ((n:ℝ)*Real.arccos c))=_
  rw [Spectral.avg_spectrumCoordinates ν (by fun_prop)]
  apply integral_congr_ae
  filter_upwards with ω
  change 2*(Waves.multiplierMap q.A q.B q.beta 0 (Spectral.cosineCoordinates ω)).im*
    Real.sin ((n:ℝ)*Real.arccos (Real.cos (ω:ℝ)))=_
  rw [Real.arccos_cos ω.property.1 ω.property.2]
  rfl

theorem sourceLag_nat_integral (q : General.Tuning) (ν : ProbabilityMeasure Frequency) (n : ℕ) :
    (∫ ω,sourceLag q (n:ℤ) ω ∂ν)=
      Waves.spectrumA (Spectral.spectrumCoordinates ν) (Waves.multiplierMap q.A q.B q.beta 0) 0 n-
      Waves.spectrumB (Spectral.spectrumCoordinates ν) (Waves.multiplierMap q.A q.B q.beta 0) n := by
  rw [spectrumA_coordinates,spectrumB_coordinates]
  change (∫ ω,sourceG q ω*(1-Real.cos ((n:ℝ)*(ω:ℝ)))-
    2*(angleMultiplier q ω).im*Real.sin ((n:ℝ)*(ω:ℝ)) ∂ν)=_
  rw [integral_sub]
  · exact (show Continuous (fun ω:Frequency => sourceG q ω*(1-Real.cos ((n:ℝ)*(ω:ℝ)))) by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (show Continuous (fun ω:Frequency => 2*(angleMultiplier q ω).im*Real.sin ((n:ℝ)*(ω:ℝ))) by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem sourceLag_neg_nat_integral (q : General.Tuning) (ν : ProbabilityMeasure Frequency) (n : ℕ) :
    (∫ ω,sourceLag q (-(n:ℤ)) ω ∂ν)=
      Waves.spectrumA (Spectral.spectrumCoordinates ν) (Waves.multiplierMap q.A q.B q.beta 0) 0 n+
      Waves.spectrumB (Spectral.spectrumCoordinates ν) (Waves.multiplierMap q.A q.B q.beta 0) n := by
  rw [spectrumA_coordinates,spectrumB_coordinates]
  have he (ω:Frequency) : sourceLag q (-(n:ℤ)) ω=sourceG q ω*(1-Real.cos ((n:ℝ)*(ω:ℝ)))+
      2*(angleMultiplier q ω).im*Real.sin ((n:ℝ)*(ω:ℝ)) := by
    simp only [sourceLag,ContinuousMap.coe_mk,Int.cast_neg,Int.cast_natCast,neg_mul,Real.cos_neg,Real.sin_neg]
    ring
  simp_rw [he]
  rw [integral_add]
  · exact (show Continuous (fun ω:Frequency => sourceG q ω*(1-Real.cos ((n:ℝ)*(ω:ℝ)))) by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (show Continuous (fun ω:Frequency => 2*(angleMultiplier q ω).im*Real.sin ((n:ℝ)*(ω:ℝ))) by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem rawSpectrum_probability_iff (q : General.Tuning) (ν : ProbabilityMeasure Frequency) :
    RawSpectrumSolution q (ν:Measure Frequency) ↔
      Waves.MixtureFeasible (Spectral.spectrumCoordinates ν) (Waves.multiplierMap q.A q.B q.beta 0) 0 0 := by
  constructor
  · rintro ⟨_,_,hG,hL⟩
    refine ⟨?_,fun n hn => ?_⟩
    · simpa only [abs_zero,spectrumG_coordinates] using hG
    · have hl := hL (n:ℤ) (by exact_mod_cast (by omega : n≠0))
      have hu := hL (-(n:ℤ)) (neg_ne_zero.mpr (by exact_mod_cast (by omega : n≠0)))
      simp only [sourceLag_nat_integral,sourceLag_neg_nat_integral] at hl hu
      simpa only [zero_mul,add_zero,sub_zero] using And.intro hl hu
  · intro h
    refine ⟨inferInstance,IsProbabilityMeasure.ne_zero _,?_,fun n hn => ?_⟩
    · simpa only [abs_zero,spectrumG_coordinates] using h.1
    · obtain ⟨m,rfl|rfl⟩ := n.eq_nat_or_neg
      · have hm : 1≤m := by omega
        have hl := (h.2 m hm).1
        simpa only [sourceLag_nat_integral,zero_mul,add_zero] using hl
      · have hm : 1≤m := by omega
        have hu := (h.2 m hm).2
        simpa only [sourceLag_neg_nat_integral,zero_mul,sub_zero] using hu

theorem threshold_spectral_iff_fp (q : General.Tuning) :
    (∃ν : Spectral.Spectrum, Waves.MixtureFeasible ν (Waves.multiplierMap q.A q.B q.beta 0) 0 0) ↔
      FP (tuningCurve q) := by
  constructor
  · rintro ⟨ν,hν⟩
    let μ := Spectral.spectrumCoordinates.symm ν
    have hμ : RawSpectrumSolution q (μ:Measure Frequency) :=
      (rawSpectrum_probability_iff q μ).mpr (by simpa only [μ,Spectral.spectrumCoordinates.apply_symm_apply] using hν)
    exact ⟨reweight (sourceDensity q) μ,(rawSpectrumSolution_iff_reweight q μ).mp hμ⟩
  · rintro ⟨w,hw⟩
    let μ := (thresholdMeasureEquiv q).symm ⟨w,hw⟩
    obtain ⟨ν,hν⟩ := μ.property.normalize
    exact ⟨Spectral.spectrumCoordinates ν,(rawSpectrum_probability_iff q ν).mp hν⟩

theorem threshold_spectral_C_iff_fp (q : General.Tuning) :
    (∃(ν : Spectral.Spectrum)(C:ℝ),Waves.MixtureFeasible ν (Waves.multiplierMap q.A q.B q.beta 0) C 0) ↔
      FP (tuningCurve q) := by
  rw [← threshold_spectral_iff_fp]
  constructor
  · rintro ⟨ν,C,hν⟩
    refine ⟨ν,?_,fun n hn => ?_⟩
    · simpa only [abs_zero] using (abs_nonneg C).trans hν.1
    · simpa only [mul_zero,Real.sinh_zero,mul_zero,add_zero,sub_zero] using hν.2 n hn
  · rintro ⟨ν,hν⟩
    exact ⟨ν,0,hν⟩

end polyak.Levels
