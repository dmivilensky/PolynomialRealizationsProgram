import polyak.Global.Threshold.Extremals
import polyak.Global.Sampling.FullSampling

/-! The unconditional global source theorems. The approximation used by
continuity and the condition-number infimum is the actual kernel-smoothing
and Fourier-sampling theorem, with all analytic premises discharged. -/
noncomputable section
namespace polyak.Global.Threshold
open General Levels Set Filter MeasureTheory

theorem periodic_threshold_finite (q : Tuning) {L : ℕ} (hL : 3≤L) :
    ∃s : ℝ,∀t : ℝ,PeriodicFP (Geometry.shiftedCurve q t) L ↔ s≤t :=
  ⟨sigmaPeriodic q L,fun t=>Levels.Threshold.shifted_periodic_iff q hL t⟩

theorem periodic_approximation (q : Tuning) (s : ℝ) (hs : sigma q<s) :
    ∃L : ℕ,3≤L ∧ sigmaPeriodic q L<s := by
  have hε : 0<(s-sigma q)/2 := by linarith
  obtain ⟨L,hL,hbound⟩ := Sampling.periodic_threshold_approximation q hε
  exact ⟨L,hL,by linarith⟩

@[fun_prop] theorem continuous_sigma : Continuous sigma :=
  continuous_sigma_of_periodic_approximation periodic_approximation

theorem kappaBoundary_le_iff (p : ParameterStrip) (κ : ConditionNumber) :
    (kappaBoundary p).val≤(κ.val:EReal) ↔ fixedThreshold p κ≤0 :=
  kappaBoundary_le_iff_of_continuous_sigma continuous_sigma p κ

theorem kappaBoundary_lt_iff (p : ParameterStrip) (κ : ConditionNumber) :
    (kappaBoundary p).val<(κ.val:EReal) ↔ fixedThreshold p κ<0 :=
  crossing_lt_iff_neg (continuous_sigma.comp continuous_tuning)
    fixedThreshold_strictAnti fixedThreshold_positive_somewhere p κ

theorem kappaBoundary_eq_iff (p : ParameterStrip) (κ : ConditionNumber) :
    (kappaBoundary p).val=(κ.val:EReal) ↔ fixedThreshold p κ=0 := by
  constructor
  · intro he
    have hle := (kappaBoundary_le_iff p κ).mp he.le
    apply le_antisymm hle
    by_contra hn
    have hlt := (kappaBoundary_lt_iff p κ).mpr (lt_of_not_ge hn)
    rw [he] at hlt
    exact lt_irrefl _ hlt
  · intro he
    have hle := (kappaBoundary_le_iff p κ).mpr he.le
    apply le_antisymm hle
    by_contra hn
    have hlt := (kappaBoundary_lt_iff p κ).mp (lt_of_not_ge hn)
    rw [he] at hlt
    exact lt_irrefl _ hlt

@[fun_prop] theorem continuous_kappaBoundary : Continuous kappaBoundary :=
  continuous_kappaBoundary_of_continuous_sigma continuous_sigma

theorem kappaBoundary_epigraph (p : ParameterStrip) (κ : ConditionNumber) :
    FP (tuningCurve (tuning p κ)) ↔ (kappaBoundary p).val≤(κ.val:EReal) :=
  kappaBoundary_epigraph_of_periodic_approximation periodic_approximation p κ

theorem divergenceSet_iff_kappaBoundary (q : Tuning) :
    q∈Regions.divergenceSet ↔ (kappaBoundary (parameters q)).val≤(q.kappa:EReal) := by
  rw [divergenceSet_iff_fp]
  have hh := kappaBoundary_epigraph (parameters q) (conditionNumber q)
  rw [tuning_parameters] at hh
  exact hh

theorem divergenceSet_eq_kappaBoundary_epigraph :
    Regions.divergenceSet={q : Tuning | (kappaBoundary (parameters q)).val≤(q.kappa:EReal)} := by
  ext q
  exact divergenceSet_iff_kappaBoundary q

theorem kappaBoundary_eq_iInf_kappaPeriodic (p : ParameterStrip) :
    (kappaBoundary p).val=⨅L : PeriodicIndex,(kappaPeriodic L p).val :=
  kappaBoundary_eq_iInf_of_periodic_approximation periodic_approximation p

theorem sigma_eq_zero_on_frontier {q : Tuning}
    (hq : q∈frontier Regions.divergenceSet) : sigma q=0 :=
  sigma_eq_zero_on_frontier_of_continuous continuous_sigma hq

theorem boundary_thresholdExtremals_eq {q : Tuning}
    (hq : q∈frontier Regions.divergenceSet) :
    thresholdExtremals q={w | ProgramSolution (tuningCurve q) nonzeroLags w} :=
  boundary_thresholdExtremals_eq_of_continuous continuous_sigma hq

/-- The finite, attained periodic thresholds and the full threshold are
continuous on the entire source tuning domain. -/
theorem global_structure_a :
    (∀L : ℕ,3≤L→
      (∀q : Tuning,∃s : ℝ,∀t : ℝ,PeriodicFP (Geometry.shiftedCurve q t) L ↔ s≤t) ∧
      Continuous (fun q : Tuning=>sigmaPeriodic q L)) ∧ Continuous sigma := by
  exact ⟨fun _ hL=>⟨fun q=>periodic_threshold_finite q hL,continuous_sigmaPeriodic hL⟩,
    continuous_sigma⟩

theorem global_structure_b (p : ParameterStrip) :
    StrictAnti (fixedThreshold p) ∧ Tendsto (fixedThreshold p) atBot atTop :=
  ⟨fixedThreshold_strictAnti p,fixedThreshold_tendsto_atBot p⟩

/-- The target is the actual order-topological subtype (1,+∞], so this
statement includes infinite boundaries and the zero-momentum edge. -/
theorem global_structure_c :
    Continuous kappaBoundary ∧
      Regions.divergenceSet={q : Tuning | (kappaBoundary (parameters q)).val≤(q.kappa:EReal)} :=
  ⟨continuous_kappaBoundary,divergenceSet_eq_kappaBoundary_epigraph⟩

theorem periodic_condition_threshold (L : PeriodicIndex) (p : ParameterStrip) :
    (∀κ : ConditionNumber,PeriodicFP (tuningCurve (tuning p κ)) L.val ↔
      (kappaPeriodic L p).val≤(κ.val:EReal)) ∧
      (kappaBoundary p).val=⨅k : PeriodicIndex,(kappaPeriodic k p).val :=
  ⟨fun κ=>kappaPeriodic_epigraph L p κ,kappaBoundary_eq_iInf_kappaPeriodic p⟩

end polyak.Global.Threshold
