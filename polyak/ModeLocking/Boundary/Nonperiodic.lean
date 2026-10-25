import polyak.ModeLocking.Boundary.Frontier

/-! At a genuinely nonperiodic boundary point EVERY sufficiently large
period has threshold tending to zero; no subsequence of periods is substituted. -/
noncomputable section
namespace polyak.ModeLocking
open General Levels Set Filter MeasureTheory
open scoped Topology

theorem nonperiodic_boundary_thresholds {K:ℕ} {q:Tuning} (hq:q∈BoundaryInGap K)
    (hn:¬PeriodicBoundary q) :
    Tendsto (fun L:ℕ=>Threshold.sigmaPeriodic q L) atTop (𝓝 0) := by
  have hfull:FP (Geometry.shiftedCurve q (Threshold.sigma q)):=Threshold.sigma_feasible q
  obtain ⟨ν,hν⟩:=(Threshold.shifted_monoform_iff q _).mp hfull
  have hNP:Global.Sampling.Nonperiodic ν:=by
    intro L hL hcar
    apply hn
    exact ⟨L,hL,by
      simpa only [boundary_sigma_zero hq] using
        Global.Sampling.sigmaPeriodic_eq_sigma_of_carried q hL hν hcar⟩
  apply tendsto_order.2
  constructor
  · intro a ha
    apply eventually_atTop.2
    refine ⟨3,fun L hL=>?_⟩
    have hlo:0≤Threshold.sigmaPeriodic q L:=by
      simpa only [boundary_sigma_zero hq] using Threshold.sigma_le_sigmaPeriodic q hL
    exact ha.trans_le hlo
  · intro b hb
    obtain ⟨L0,_hL0,hbound⟩:=Global.Sampling.eventual_sigmaPeriodic_le_add_of_nonperiodic q hν hNP
      (show 0<b/2 by positivity)
    apply eventually_atTop.2
    refine ⟨L0,fun L hL=>?_⟩
    have hh:=hbound L hL
    rw [boundary_sigma_zero hq,zero_add] at hh
    linarith


end polyak.ModeLocking
