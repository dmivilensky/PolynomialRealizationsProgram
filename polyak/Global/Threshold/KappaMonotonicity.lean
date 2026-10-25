import polyak.Global.Threshold.PeriodicContinuity
import polyak.Levels.Threshold.Kappa

/-! Actual strict condition-number monotonicity, with a quantitative shift
margin uniform over the full frequency interval. -/
noncomputable section
namespace polyak.Global.Threshold
open General Levels

theorem sigma_strictAnti_kappa (q p : Tuning) (hy : p.y=q.y) (hb : p.beta=q.beta)
    (hκ : q.kappa<p.kappa) : sigma p<sigma q := by
  obtain ⟨ε,hε,hgap⟩:=Levels.exists_uniform_cotangent_kappa_gap q p hy hb hκ
  have hh:=Levels.Threshold.sigma_shift_compare hgap
  linarith

theorem sigmaPeriodic_strictAnti_kappa (q p : Tuning) (hy : p.y=q.y) (hb : p.beta=q.beta)
    (hκ : q.kappa<p.kappa) {k : ℕ} (hk : 3≤k) : sigmaPeriodic p k<sigmaPeriodic q k := by
  obtain ⟨ε,hε,hgap⟩:=Levels.exists_uniform_cotangent_kappa_gap q p hy hb hκ
  have hh:=Levels.Threshold.sigmaPeriodic_shift_compare hk hgap
  linarith

end polyak.Global.Threshold
