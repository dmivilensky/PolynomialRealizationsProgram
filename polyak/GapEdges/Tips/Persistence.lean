import polyak.GapEdges.Tips.Certificate
import polyak.GapEdges.Specialization.FirstTongue
import polyak.ModeLocking.Modelock.Results
import polyak.Levels.Geometry.LagOne
import polyak.Levels.Realization.ThresholdSets

/-! Full tip neighborhoods: the constructed regular certificate persists,
and its fixed singleton support forces the explicit analytic shift. -/
noncomputable section
namespace polyak.GapEdges
open General Levels ModeLocking Set Filter MeasureTheory
open scoped Topology BigOperators

theorem phase_half_of_lag_one_zero (Θ : Curve) {ω : Frequency}
    (hω : 0 < (ω : ℝ)) (hz : Θ.lag 1 ω = 0) : Θ ω = (ω : ℝ) / 2 := by
  apply le_antisymm
  · by_contra h
    have hh := (Geometry.lag_one_neg_iff Θ ω).mpr ⟨hω, lt_of_not_ge h⟩
    linarith
  · by_contra h
    have hh := (Geometry.lag_one_pos_iff Θ ω).mpr (lt_of_not_ge h)
    linarith

namespace Tip
variable {q : Tuning} {k : ℕ} (T : Tip q k)
include T

theorem persistence : ∀ᶠ q' in 𝓝 q,
    ∃ D : RegularData q' (Threshold.sigma q') k,
      Set.range D.atoms = {T.frequency} ∧ D.lags = lags k ∧
      Threshold.sigma q' = FareyPlateau.Edge.shift q' k (2 * Real.pi / k) ∧
      Threshold.sigmaPeriodic q' k = FareyPlateau.Edge.shift q' k (2 * Real.pi / k) := by
  obtain ⟨D₀, hsupport, hlags⟩ := T.regular_at_tip
  filter_upwards [D₀.regular_persistence] with q' hq'
  obtain ⟨D, hatoms, _, hN⟩ := hq'
  have hsupp : Set.range D.atoms = {T.frequency} := hatoms.trans hsupport
  have hN' : D.lags = lags k := hN.trans hlags
  have hsame (i : Fin D.d) : D.atoms i = T.frequency := by
    have hm : D.atoms i ∈ Set.range D.atoms := ⟨i, rfl⟩
    simpa only [hsupp, mem_singleton_iff] using hm
  have htight := D.lag_tight 1 (by rw [hN']; simp [lags])
  have hsum : (∑ i, (D.primal i : ℝ)) = 1 := by exact_mod_cast D.primal_sum
  simp only [hsame, ← Finset.sum_mul, hsum, one_mul] at htight
  have hphase := phase_half_of_lag_one_zero (Geometry.shiftedCurve q' (Threshold.sigma q'))
    T.frequency_mem.1 htight
  change Geometry.shiftedAngle q' (Threshold.sigma q') (T.frequency : ℝ) = (T.frequency : ℝ) / 2 at hphase
  rw [T.frequency_coe] at hphase
  have hp : Geometry.shiftedAngle q' (Threshold.sigma q') (2 * Real.pi / k) = Real.pi / k := by
    calc
      _ = (2 * Real.pi / (k : ℝ)) / 2 := hphase
      _ = Real.pi / k := by ring
  have hcot := Geometry.cot_shiftedAngle q' (Threshold.sigma q')
    (by simpa only [T.frequency_coe] using T.frequency_mem)
  rw [hp] at hcot
  have hshift : Threshold.sigma q' = FareyPlateau.Edge.shift q' k (2 * Real.pi / k) := by
    unfold FareyPlateau.Edge.shift Geometry.cotangent
    linarith
  exact ⟨D, hsupp, hN', hshift, D.sigmaPeriodic_eq.trans hshift⟩

theorem closed_tongue_near : ∀ᶠ q' in 𝓝 q,
    (q' ∈ Regions.divergenceSet ↔ q'.angle (2 * Real.pi / k) ≤ Real.pi / k) ∧
      (∀ K : ℕ, Geometry.Gap K q' → 0 < Threshold.sigma q') := by
  filter_upwards [T.persistence] with q' hq'
  obtain ⟨D, _, _, he, _⟩ := hq'
  refine ⟨?_, ?_⟩
  · rw [divergenceSet_iff_sigma_nonpos, he]
    exact first_shift_nonpos_iff q' T.period_ge
  · intro K hK
    rw [he]
    exact first_shift_pos_in_every_gap hK T.period_ge

theorem extremals_near : ∀ᶠ q' in 𝓝 q,
    ∀ w : Measure Frequency,
      ProgramSolution (Geometry.shiftedCurve q' (Threshold.sigma q')) nonzeroLags w ↔
        ∃ c a : NNReal, 0 < c ∧
          w = (c : ENNReal) • Measure.dirac T.frequency +
            (a : ENNReal) • Measure.dirac frequencyZero ∧
          (a : ℝ) ≤ (c : ℝ) * (Geometry.shiftedCurve q' (Threshold.sigma q')).minimizer T.frequency := by
  filter_upwards [T.persistence] with q' hq'
  obtain ⟨D, hsupp, _, _, _⟩ := hq'
  have hsame (i : Fin D.d) : D.atoms i = T.frequency := by
    have hm : D.atoms i ∈ Set.range D.atoms := ⟨i, rfl⟩
    simpa only [hsupp, mem_singleton_iff] using hm
  have hm : D.measure = Measure.dirac T.frequency := by
    unfold RegularData.measure atomicMeasure
    simp only [hsame, ← Finset.sum_smul, ← ENNReal.ofNNReal_finsetSum, D.primal_sum,
      ENNReal.coe_one, one_smul]
  intro w
  simpa only [hm, integral_dirac] using
    D.extremal_iff (N' := nonzeroLags) (fun n hn => D.lags_nonzero n hn) (fun _ h => h) w

theorem analytic_threshold_near :
    ∃ f : Continuation.Parameters → ℝ, ∀ᶠ q' in 𝓝 q,
      AnalyticAt ℝ f (Continuation.parameters q') ∧
        Threshold.sigma q' = f (Continuation.parameters q') := by
  obtain ⟨D, _, _⟩ := T.regular_at_tip
  obtain ⟨C⟩ := D.continuationData_nonempty
  refine ⟨C.shift, ?_⟩
  filter_upwards [C.localData_near] with q' hq'
  obtain ⟨A⟩ := hq'
  exact ⟨analyticAt_fst.comp (f := C.primalShift) A.analytic_primalShift, A.sigma_eq⟩

end Tip
end polyak.GapEdges
