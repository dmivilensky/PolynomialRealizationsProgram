import polyak.Levels.Threshold.ClosedProgram
import polyak.Levels.Threshold.ShiftOrder
import polyak.Levels.Threshold.MonoformMonotonicity
import polyak.Levels.Program.FiniteAtoms
import Mathlib.Topology.Order.Monotone

/-! Finite attained thresholds, their closed epigraph and shift comparison. -/
noncomputable section
open MeasureTheory
namespace polyak.Levels.Threshold

def feasibleShifts (q : General.Tuning) (𝒩 : Set ℤ) : Set ℝ :=
  {s | FPOn (Geometry.shiftedCurve q s) 𝒩}

def sigmaOn (q : General.Tuning) (𝒩 : Set ℤ) : ℝ := sInf (feasibleShifts q 𝒩)
def sigma (q : General.Tuning) : ℝ := sigmaOn q nonzeroLags

theorem feasibleShifts_nonempty (q : General.Tuning) (𝒩 : Set ℤ) (hN : 𝒩⊆nonzeroLags) :
    (feasibleShifts q 𝒩).Nonempty := shifted_fpOn_nonempty q 𝒩 hN

theorem feasibleShifts_bddBelow (q : General.Tuning) (𝒩 : Set ℤ) :
    BddBelow (feasibleShifts q 𝒩) := ⟨-Geometry.cotangentUpper q,fun _ hs => shifted_fpOn_lower_bound q 𝒩 hs⟩

theorem feasibleShifts_isClosed (q : General.Tuning) (𝒩 : Set ℤ) : IsClosed (feasibleShifts q 𝒩) :=
  (isClosed_shifted_fpOn 𝒩).preimage (continuous_const.prodMk continuous_id)

theorem sigmaOn_feasible (q : General.Tuning) (𝒩 : Set ℤ) (hN : 𝒩⊆nonzeroLags) :
    FPOn (Geometry.shiftedCurve q (sigmaOn q 𝒩)) 𝒩 :=
  (feasibleShifts_isClosed q 𝒩).csInf_mem (feasibleShifts_nonempty q 𝒩 hN) (feasibleShifts_bddBelow q 𝒩)

theorem shifted_feasible_iff (q : General.Tuning) (𝒩 : Set ℤ) (hN : 𝒩⊆nonzeroLags) (s : ℝ) :
    FPOn (Geometry.shiftedCurve q s) 𝒩 ↔ sigmaOn q 𝒩≤s := by
  constructor
  · intro hs
    exact csInf_le (feasibleShifts_bddBelow q 𝒩) hs
  · intro hs
    exact shifted_fpOn_mono q 𝒩 hs (sigmaOn_feasible q 𝒩 hN)

theorem shifted_fp_iff (q : General.Tuning) (s : ℝ) :
    FP (Geometry.shiftedCurve q s) ↔ sigma q≤s := shifted_feasible_iff q nonzeroLags (fun _ h=>h) s

theorem sigma_feasible (q : General.Tuning) : FP (Geometry.shiftedCurve q (sigma q)) :=
  sigmaOn_feasible q nonzeroLags (fun _ h=>h)

theorem fp_iff_sigma_nonpos (q : General.Tuning) : FP (tuningCurve q) ↔ sigma q≤0 := by
  rw [← Geometry.shiftedCurve_zero q]
  exact shifted_fp_iff q 0

theorem isClosed_sigmaOn_epigraph (𝒩 : Set ℤ) (hN : 𝒩⊆nonzeroLags) :
    IsClosed {p:General.Tuning×ℝ | sigmaOn p.1 𝒩≤p.2} := by
  have he : {p:General.Tuning×ℝ | sigmaOn p.1 𝒩≤p.2}=
      {p:General.Tuning×ℝ | FPOn (Geometry.shiftedCurve p.1 p.2) 𝒩} := by
    ext p
    exact (shifted_feasible_iff p.1 𝒩 hN p.2).symm
  rw [he]
  exact isClosed_shifted_fpOn 𝒩

theorem isClosed_sigma_epigraph : IsClosed {p:General.Tuning×ℝ | sigma p.1≤p.2} :=
  isClosed_sigmaOn_epigraph nonzeroLags (fun _ h=>h)

theorem sigmaOn_shift_compare {q q' : General.Tuning} (𝒩 : Set ℤ) (hN : 𝒩⊆nonzeroLags)
    {e : ℝ} (h : ∀ω∈Set.Ioo 0 Real.pi,Geometry.cotangent q ω+e≤Geometry.cotangent q' ω) :
    sigmaOn q' 𝒩≤sigmaOn q 𝒩-e := by
  apply (shifted_feasible_iff q' 𝒩 hN _).mp
  apply fpOn_mono 𝒩 (shiftedCurve_le_of_cotangent_le ?_) (sigmaOn_feasible q 𝒩 hN)
  intro ω hω
  linarith [h ω hω]

theorem sigma_shift_compare {q q' : General.Tuning} {e : ℝ}
    (h : ∀ω∈Set.Ioo 0 Real.pi,Geometry.cotangent q ω+e≤Geometry.cotangent q' ω) :
    sigma q'≤sigma q-e := sigmaOn_shift_compare nonzeroLags (fun _ h=>h) h

theorem sigmaOn_le_sigma (q : General.Tuning) (𝒩 : Set ℤ) (hN : 𝒩⊆nonzeroLags) :
    sigmaOn q 𝒩≤sigma q := by
  apply (shifted_feasible_iff q 𝒩 hN _).mp
  exact (sigma_feasible q).relax hN

theorem periodicFP_iff_probability (Θ : Curve) (k : ℕ) :
    PeriodicFP Θ k ↔ ∃ν:ProbabilityMeasure Frequency,
      ProbabilitySolution Θ nonzeroLags ν ∧ (∀ᵐω∂(ν:Measure Frequency),ω∈periodicGrid k) := by
  constructor
  · rintro ⟨w,hw,hcar⟩
    exact hw.normalize_carried hcar
  · rintro ⟨ν,hν,hcar⟩
    exact ⟨ν,hν.toProgramSolution,hcar⟩

theorem shifted_periodic_mono (q : General.Tuning) (k : ℕ) {s t:ℝ} (hst:s≤t)
    (hs:PeriodicFP (Geometry.shiftedCurve q s) k) : PeriodicFP (Geometry.shiftedCurve q t) k := by
  obtain ⟨ν,hν,hcar⟩ := (shifted_monoform_carried_iff q s (periodicGrid k)).mp hs
  have hh : Measurable (shiftedCotangent q t) := by
    unfold shiftedCotangent Geometry.cotangent General.Tuning.Xi
    fun_prop
  have hle : ∀ᵐω∂ν,shiftedCotangent q s ω≤shiftedCotangent q t ω :=
    Filter.Eventually.of_forall (fun ω => by dsimp [shiftedCotangent]; linarith)
  have hbound : ∀ᵐω∂ν,shiftedCotangent q t ω≤Geometry.cotangentUpper q+t :=
    hν.2.2.1.mono fun ω hω => by dsimp [shiftedCotangent]; linarith [Geometry.cotangent_le_upper q hω]
  have hν' := (hν.mono_ae hh.aestronglyMeasurable hle hbound).1
  exact (shifted_monoform_carried_iff q t (periodicGrid k)).mpr ⟨ν,hν',hcar⟩

def periodicFeasibleShifts (q : General.Tuning) (k : ℕ) : Set ℝ :=
  {s | PeriodicFP (Geometry.shiftedCurve q s) k}

def sigmaPeriodic (q : General.Tuning) (k : ℕ) : ℝ := sInf (periodicFeasibleShifts q k)

theorem periodicGrid_nonempty {k : ℕ} (hk : 2≤k) : (periodicGrid k).Nonempty :=
  ⟨periodicFrequency k hk,periodicFrequency_mem_grid hk⟩

theorem periodicFeasibleShifts_isClosed (q : General.Tuning) {k : ℕ} (hk : 3≤k) :
    IsClosed (periodicFeasibleShifts q k) := by
  have hc : Continuous (fun p:ℝ×Frequency => Geometry.shiftedCurve q p.1 p.2) := by
    have hg : Continuous (fun p:ℝ×Frequency => ((q,p.1),p.2)) :=
      (continuous_const.prodMk continuous_fst).prodMk continuous_snd
    have ht := shiftedCurve_jointContinuous.comp hg
    exact ht.congr (fun _ => rfl)
  have hs := isClosed_supported_family (fun s=>Geometry.shiftedCurve q s) hc nonzeroLags
    (periodicGrid_finite (by omega : 0<k)).isClosed (periodicGrid_nonempty (by omega))
  have he : periodicFeasibleShifts q k=
      {s | ∃ν:ProbabilityMeasure Frequency,ProbabilitySolution (Geometry.shiftedCurve q s) nonzeroLags ν ∧
        (∀ᵐω∂(ν:Measure Frequency),ω∈periodicGrid k)} := by
    ext s
    exact periodicFP_iff_probability _ _
  rw [he]
  exact hs

theorem periodicFeasibleShifts_bddBelow (q : General.Tuning) (k : ℕ) :
    BddBelow (periodicFeasibleShifts q k) := by
  refine ⟨-Geometry.cotangentUpper q,fun s hs=>?_⟩
  exact shifted_fpOn_lower_bound q nonzeroLags hs.fp

theorem sigmaPeriodic_feasible (q : General.Tuning) {k : ℕ} (hk : 3≤k) :
    PeriodicFP (Geometry.shiftedCurve q (sigmaPeriodic q k)) k :=
  (periodicFeasibleShifts_isClosed q hk).csInf_mem (shifted_periodic_nonempty q hk)
    (periodicFeasibleShifts_bddBelow q k)

theorem shifted_periodic_iff (q : General.Tuning) {k : ℕ} (hk : 3≤k) (s : ℝ) :
    PeriodicFP (Geometry.shiftedCurve q s) k ↔ sigmaPeriodic q k≤s := by
  constructor
  · intro hs
    exact csInf_le (periodicFeasibleShifts_bddBelow q k) hs
  · intro hs
    exact shifted_periodic_mono q k hs (sigmaPeriodic_feasible q hk)

theorem sigma_le_sigmaPeriodic (q : General.Tuning) {k : ℕ} (hk : 3≤k) :
    sigma q≤sigmaPeriodic q k :=
  (shifted_fp_iff q _).mp (sigmaPeriodic_feasible q hk).fp

end polyak.Levels.Threshold
