import polyak.Global.Threshold.Crossing
import polyak.Global.Threshold.NearOne
import polyak.Levels.Geometry.LevelZero

/-! The original condition-number thresholds, including their infinite
values at zero momentum. Periodic epigraphs and continuity are unconditional;
the full boundary continuity consumes actual sigma continuity in the final
sampling wrapper. -/
noncomputable section
namespace polyak.Global.Threshold
open General Levels Set

abbrev PeriodicIndex := Set.Ici (3:ℕ)

def kappaBoundary (p : ParameterStrip) : ExtendedConditionNumber :=
  crossingCondition fixedThreshold fixedThreshold_strictAnti fixedThreshold_positive_somewhere p

def kappaPeriodic (k : PeriodicIndex) (p : ParameterStrip) : ExtendedConditionNumber :=
  crossingCondition (fixedPeriodicThreshold k.val) (fun p=>fixedPeriodicThreshold_strictAnti p k.property)
    (fixedPeriodicThreshold_positive_somewhere k.property) p

theorem kappaBoundary_gt_one (p : ParameterStrip) : (1:EReal)<(kappaBoundary p).val :=
  (kappaBoundary p).property

theorem kappaPeriodic_gt_one (k : PeriodicIndex) (p : ParameterStrip) :
    (1:EReal)<(kappaPeriodic k p).val := (kappaPeriodic k p).property

theorem kappaBoundary_le_iff_of_continuous_sigma (hσ : Continuous sigma)
    (p : ParameterStrip) (κ : ConditionNumber) :
    (kappaBoundary p).val≤(κ.val:EReal) ↔ fixedThreshold p κ≤0 :=
  crossing_le_iff_nonpos (hσ.comp continuous_tuning) fixedThreshold_strictAnti p κ

theorem continuous_kappaBoundary_of_continuous_sigma (hσ : Continuous sigma) :
    Continuous kappaBoundary :=
  continuous_crossingCondition (hσ.comp continuous_tuning) fixedThreshold_strictAnti fixedThreshold_positive_somewhere

theorem kappaPeriodic_le_iff (k : PeriodicIndex) (p : ParameterStrip) (κ : ConditionNumber) :
    (kappaPeriodic k p).val≤(κ.val:EReal) ↔ fixedPeriodicThreshold k.val p κ≤0 :=
  crossing_le_iff_nonpos (continuous_fixedPeriodicThreshold k.property)
    (fun p=>fixedPeriodicThreshold_strictAnti p k.property) p κ

theorem kappaPeriodic_epigraph (k : PeriodicIndex) (p : ParameterStrip) (κ : ConditionNumber) :
    PeriodicFP (tuningCurve (tuning p κ)) k.val ↔ (kappaPeriodic k p).val≤(κ.val:EReal) := by
  rw [kappaPeriodic_le_iff]
  simpa only [fixedPeriodicThreshold,←Geometry.shiftedCurve_zero (tuning p κ)] using
    Levels.Threshold.shifted_periodic_iff (tuning p κ) k.property 0

theorem continuous_kappaPeriodic (k : PeriodicIndex) : Continuous (kappaPeriodic k) :=
  continuous_crossingCondition (continuous_fixedPeriodicThreshold k.property)
    (fun p=>fixedPeriodicThreshold_strictAnti p k.property)
    (fixedPeriodicThreshold_positive_somewhere k.property)

theorem sigma_pos_of_beta_zero (q : Tuning) (hb : q.beta=0) : 0<sigma q := by
  have hΩ : Regions.OmegaOne q:=(Regions.omegaOne_iff_explicit q).mpr (Or.inl hb)
  have he : Geometry.closedDip (tuningCurve q)=∅:=(Geometry.closedDip_empty_iff_omegaOne q).mpr hΩ
  apply lt_of_not_ge
  intro hn
  obtain ⟨w,hw⟩:=(Levels.Threshold.fp_iff_sigma_nonpos q).mpr hn
  have hm:=Geometry.full_solution_closedDip_mass_pos hw
  rw [he,MeasureTheory.measure_empty] at hm
  exact lt_irrefl _ hm

theorem kappaBoundary_eq_top_iff (p : ParameterStrip) :
    (kappaBoundary p).val=⊤ ↔ ∀κ : ConditionNumber,0<fixedThreshold p κ :=
  crossing_eq_top_iff fixedThreshold p

theorem kappaPeriodic_eq_top_iff (k : PeriodicIndex) (p : ParameterStrip) :
    (kappaPeriodic k p).val=⊤ ↔ ∀κ : ConditionNumber,0<fixedPeriodicThreshold k.val p κ :=
  crossing_eq_top_iff (fixedPeriodicThreshold k.val) p

theorem kappaBoundary_top_of_beta_zero (p : ParameterStrip) (hb : p.val.2=0) :
    (kappaBoundary p).val=⊤ := by
  apply (kappaBoundary_eq_top_iff p).mpr
  intro κ
  exact sigma_pos_of_beta_zero (tuning p κ) hb

theorem kappaPeriodic_top_of_beta_zero (k : PeriodicIndex) (p : ParameterStrip) (hb : p.val.2=0) :
    (kappaPeriodic k p).val=⊤ := by
  apply (kappaPeriodic_eq_top_iff k p).mpr
  intro κ
  exact (sigma_pos_of_beta_zero (tuning p κ) hb).trans_le
    (Levels.Threshold.sigma_le_sigmaPeriodic (tuning p κ) k.property)

end polyak.Global.Threshold
