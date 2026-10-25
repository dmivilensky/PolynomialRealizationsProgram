import polyak.Levels.Threshold.ShiftThreshold

/-! Joint closedness and shift comparison also hold for every periodic program. -/
noncomputable section
open MeasureTheory
namespace polyak.Levels.Threshold

theorem isClosed_shifted_periodic {k : ℕ} (hk : 3≤k) :
    IsClosed {p:General.Tuning×ℝ | PeriodicFP (Geometry.shiftedCurve p.1 p.2) k} := by
  have hs := isClosed_supported_family
    (fun p:General.Tuning×ℝ=>Geometry.shiftedCurve p.1 p.2) shiftedCurve_jointContinuous nonzeroLags
    (periodicGrid_finite (by omega : 0<k)).isClosed (periodicGrid_nonempty (by omega))
  have he : {p:General.Tuning×ℝ | PeriodicFP (Geometry.shiftedCurve p.1 p.2) k}=
      {p:General.Tuning×ℝ | ∃ν:ProbabilityMeasure Frequency,
        ProbabilitySolution (Geometry.shiftedCurve p.1 p.2) nonzeroLags ν ∧
          (∀ᵐω∂(ν:Measure Frequency),ω∈periodicGrid k)} := by
    ext p
    exact periodicFP_iff_probability _ _
  rw [he]
  exact hs

theorem isClosed_sigmaPeriodic_epigraph {k : ℕ} (hk : 3≤k) :
    IsClosed {p:General.Tuning×ℝ | sigmaPeriodic p.1 k≤p.2} := by
  have he : {p:General.Tuning×ℝ | sigmaPeriodic p.1 k≤p.2}=
      {p:General.Tuning×ℝ | PeriodicFP (Geometry.shiftedCurve p.1 p.2) k} := by
    ext p
    exact (shifted_periodic_iff p.1 hk p.2).symm
  rw [he]
  exact isClosed_shifted_periodic hk

theorem shifted_periodic_compare {q q' : General.Tuning} (k : ℕ) {s t:ℝ}
    (horder : ∀ω∈Set.Ioo 0 Real.pi,Geometry.cotangent q ω+s≤Geometry.cotangent q' ω+t)
    (hs : PeriodicFP (Geometry.shiftedCurve q s) k) : PeriodicFP (Geometry.shiftedCurve q' t) k := by
  obtain ⟨ν,hν,hcar⟩ := (shifted_monoform_carried_iff q s (periodicGrid k)).mp hs
  have hh : Measurable (shiftedCotangent q' t) := by
    unfold shiftedCotangent Geometry.cotangent General.Tuning.Xi
    fun_prop
  have hle : ∀ᵐω∂ν,shiftedCotangent q s ω≤shiftedCotangent q' t ω :=
    hν.2.2.1.mono fun ω hω => horder ω hω
  have hbound : ∀ᵐω∂ν,shiftedCotangent q' t ω≤Geometry.cotangentUpper q'+t :=
    hν.2.2.1.mono fun ω hω => by dsimp [shiftedCotangent]; linarith [Geometry.cotangent_le_upper q' hω]
  exact (shifted_monoform_carried_iff q' t (periodicGrid k)).mpr
    ⟨ν,(hν.mono_ae hh.aestronglyMeasurable hle hbound).1,hcar⟩

theorem sigmaPeriodic_shift_compare {q q' : General.Tuning} {k : ℕ} (hk : 3≤k) {e : ℝ}
    (h : ∀ω∈Set.Ioo 0 Real.pi,Geometry.cotangent q ω+e≤Geometry.cotangent q' ω) :
    sigmaPeriodic q' k≤sigmaPeriodic q k-e := by
  apply (shifted_periodic_iff q' hk _).mp
  apply shifted_periodic_compare k (hs:=sigmaPeriodic_feasible q hk)
  intro ω hω
  linarith [h ω hω]

theorem sigmaOn_mono_lags (q : General.Tuning) {𝒩 ℳ:Set ℤ} (hM:ℳ⊆nonzeroLags) (hsub:𝒩⊆ℳ) :
    sigmaOn q 𝒩≤sigmaOn q ℳ := by
  apply (shifted_feasible_iff q 𝒩 (hsub.trans hM) _).mp
  exact (sigmaOn_feasible q ℳ hM).relax hsub

end polyak.Levels.Threshold
