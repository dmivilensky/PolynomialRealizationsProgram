import polyak.Global.Threshold.Boundary

/-! The exact infimum of the original periodic condition-number
thresholds, including all infinite-value cases. The final source wrapper
supplies the proved actual periodic sampling approximation. -/
noncomputable section
namespace polyak.Global.Threshold
open General Levels Set

theorem kappaBoundary_le_kappaPeriodic (p : ParameterStrip) (k : PeriodicIndex) :
    (kappaBoundary p).val≤(kappaPeriodic k p).val := by
  apply le_sInf
  rintro z ⟨κ,rfl,hκ⟩
  exact crossing_le_of_nonpos fixedThreshold p
    ((Levels.Threshold.sigma_le_sigmaPeriodic (tuning p κ) k.property).trans hκ)

theorem kappaBoundary_eq_iInf_of_periodic_approximation
    (happrox : ∀q : Tuning,∀s : ℝ,sigma q<s→∃k : ℕ,3≤k ∧ sigmaPeriodic q k<s)
    (p : ParameterStrip) :
    (kappaBoundary p).val=⨅k : PeriodicIndex,(kappaPeriodic k p).val := by
  have hσ:=continuous_sigma_of_periodic_approximation happrox
  refine le_antisymm (le_iInf fun k=>kappaBoundary_le_kappaPeriodic p k) ?_
  by_contra hn
  have hlt : (kappaBoundary p).val<⨅k : PeriodicIndex,(kappaPeriodic k p).val:=lt_of_not_ge hn
  obtain ⟨r,hrlo,hrhi⟩:=EReal.exists_between_coe_real hlt
  have hr : 1<r:=EReal.coe_lt_coe_iff.mp ((kappaBoundary_gt_one p).trans hrlo)
  let κ : ConditionNumber:=⟨r,hr⟩
  have hf : fixedThreshold p κ<0:=
    (crossing_lt_iff_neg (hσ.comp continuous_tuning) fixedThreshold_strictAnti fixedThreshold_positive_somewhere p κ).mp hrlo
  obtain ⟨k,hk,hperiodic⟩:=happrox (tuning p κ) 0 hf
  let L : PeriodicIndex:=⟨k,hk⟩
  have hp : (kappaPeriodic L p).val≤(r:EReal):=
    (kappaPeriodic_le_iff L p κ).mpr hperiodic.le
  have hh : (r:EReal)<(r:EReal):=hrhi.trans_le ((iInf_le (fun k : PeriodicIndex=>(kappaPeriodic k p).val) L).trans hp)
  exact lt_irrefl _ hh

theorem continuous_kappaBoundary_of_periodic_approximation
    (happrox : ∀q : Tuning,∀s : ℝ,sigma q<s→∃k : ℕ,3≤k ∧ sigmaPeriodic q k<s) :
    Continuous kappaBoundary :=
  continuous_kappaBoundary_of_continuous_sigma (continuous_sigma_of_periodic_approximation happrox)

theorem kappaBoundary_epigraph_of_periodic_approximation
    (happrox : ∀q : Tuning,∀s : ℝ,sigma q<s→∃k : ℕ,3≤k ∧ sigmaPeriodic q k<s)
    (p : ParameterStrip) (κ : ConditionNumber) :
    FP (tuningCurve (tuning p κ)) ↔ (kappaBoundary p).val≤(κ.val:EReal) := by
  rw [kappaBoundary_le_iff_of_continuous_sigma (continuous_sigma_of_periodic_approximation happrox)]
  exact Levels.Threshold.fp_iff_sigma_nonpos (tuning p κ)

end polyak.Global.Threshold
