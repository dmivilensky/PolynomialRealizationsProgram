import polyak.Farey.Examples.ThirteenContracts

/-! The literal two-harmonic limit of the actual from-rest realization.
The Euclidean isometry preserves both nonzero orthogonal planar modes. -/
noncomputable section
namespace polyak.CertifiedExamples.Rational
open polyak.Farey.Examples polyak.Levels polyak.Dynamics MeasureTheory Filter
open scoped Topology

def thirteenHarmonics (n:ℕ) : EuclideanSpace ℂ Bool :=
  Waves.finitePosition thirteenNuWeight (fun b=>Spectral.cosineCoordinates (thirteenFrequency b)) 0 (some n)

theorem thirteenHarmonics_apply (n:ℕ) (b:Bool) :
    thirteenHarmonics n b=Real.sqrt (thirteenNuWeight b:ℝ) •
      Waves.z 0 (2*Real.pi*(if b then (2:ℝ) else 3)/13)^n := by
  rw [thirteenHarmonics,Waves.finitePosition_apply]
  change Real.sqrt (thirteenNuWeight b:ℝ) •
    Waves.z 0 (Real.arccos (Real.cos (thirteenFrequency b:ℝ)))^n=_
  rw [Real.arccos_cos (thirteenFrequency b).property.1 (thirteenFrequency b).property.2]
  rfl

theorem thirteen_harmonic_amplitudes_pos (b:Bool) : 0<Real.sqrt (thirteenNuWeight b:ℝ) := by
  apply Real.sqrt_pos.mpr
  cases b <;> norm_num [thirteenNuWeight]

theorem thirteenHarmonics_periodic : Function.Periodic thirteenHarmonics 13 := by
  apply finite_wave_periodic
  intro b
  change Waves.z 0 (Real.arccos (Real.cos (thirteenFrequency b:ℝ)))^13=1
  rw [Real.arccos_cos (thirteenFrequency b).property.1 (thirteenFrequency b).property.2]
  exact root_unity_of_mem_periodicGrid (thirteen_frequency_on_grid b)

theorem thirteen_harmonic_startup (hnum:ThirteenFiniteSigns) :
    ∃f:EuclideanSpace ℝ (Fin 5)→ℝ,
      CenteredSmoothStronglyConvex thirteenTuning.x thirteenTuning.y f ∧
      ∃x₀,x₀≠0 ∧ ∃c₀:ℝ,0<c₀ ∧
      ∃Q:EuclideanSpace ℂ Bool→ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 5),
        (∀n,c₀*‖x₀‖≤‖iterate (gradient f) 1 thirteenTuning.beta x₀ n‖) ∧
        Function.Periodic (fun n=>Q (thirteenHarmonics n)) 13 ∧
        Tendsto (fun n=>iterate (gradient f) 1 thirteenTuning.beta x₀ n-
          Q (thirteenHarmonics n)) atTop (𝓝 0) := by
  let μ:ProbabilityMeasure Frequency:=⟨thirteenNu,inferInstance⟩
  have hraw : RawSpectrumSolution thirteenTuning (μ:Measure Frequency) :=
    (thirteen_from_finite_signs hnum).1
  have he : Spectral.spectrumCoordinates μ=Waves.finiteSpectrum thirteenNuWeight
      (fun b=>Spectral.cosineCoordinates (thirteenFrequency b)) thirteen_nu_weights_sum := by
    apply Subtype.ext
    change Measure.map Spectral.cosineCoordinates (atomicMeasure thirteenNuWeight thirteenFrequency)=_
    simp only [atomicMeasure,Waves.finiteSpectrum]
    rw [Measure.map_finset_sum' Spectral.cosineCoordinates.measurable.aemeasurable]
    apply Finset.sum_congr rfl
    intro b _
    rw [Measure.map_smul _ Spectral.cosineCoordinates.measurable.aemeasurable,
      Measure.map_dirac' Spectral.cosineCoordinates.measurable]
  have hν := (rawSpectrum_probability_iff thirteenTuning μ).mp hraw
  rw [he] at hν
  have hnorm : Waves.MixtureFeasible
      (Waves.finiteSpectrum thirteenNuWeight (fun b=>Spectral.cosineCoordinates (thirteenFrequency b))
        thirteen_nu_weights_sum)
      (Waves.multiplierMap (normalizedA thirteenTuning.x thirteenTuning.y 1 thirteenTuning.beta)
        (normalizedB thirteenTuning.x thirteenTuning.y 1) thirteenTuning.beta 0) 0 0 := by
    simpa only [thirteenTuning.normalizedA_eq,thirteenTuning.normalizedB_eq] using hν
  obtain ⟨f,hf,x₀,hx,c₀,hc,Q,hb,hl⟩ := exists_finite_threshold_startup
    thirteenTuning.x_pos thirteenTuning.x_lt_y (by norm_num : (0:ℝ)<1)
    thirteenTuning.beta_nonneg thirteenTuning.beta_lt_one (by simpa using thirteenTuning.y_lt)
    thirteenNuWeight (fun b=>Spectral.cosineCoordinates (thirteenFrequency b)) thirteen_nu_weights_sum hnorm
  have hfull : ∃f:EuclideanSpace ℝ (Fin (2*Fintype.card Bool+1))→ℝ,
      CenteredSmoothStronglyConvex thirteenTuning.x thirteenTuning.y f ∧
      ∃x₀,x₀≠0 ∧ ∃c₀:ℝ,0<c₀ ∧
      ∃Q:EuclideanSpace ℂ Bool→ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2*Fintype.card Bool+1)),
        (∀n,c₀*‖x₀‖≤‖iterate (gradient f) 1 thirteenTuning.beta x₀ n‖) ∧
        Function.Periodic (fun n=>Q (thirteenHarmonics n)) 13 ∧
        Tendsto (fun n=>iterate (gradient f) 1 thirteenTuning.beta x₀ n-
          Q (thirteenHarmonics n)) atTop (𝓝 0) := by
    refine ⟨f,hf,x₀,hx,c₀,hc,Q,hb,?_,hl⟩
    intro n
    exact congrArg Q (thirteenHarmonics_periodic n)
  rw [Fintype.card_bool] at hfull
  exact hfull

end polyak.CertifiedExamples.Rational
