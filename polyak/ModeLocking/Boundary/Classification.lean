import polyak.ModeLocking.Boundary.Frontier
import polyak.Levels.Realization.ExactThreshold

/-! Finite witnesses on both sides of the true boundary, with no regularity premise. -/
noncomputable section
namespace polyak.ModeLocking
open General Levels Set Filter MeasureTheory

theorem periodicGrid_mono_dvd {L M:ℕ} (h:L∣M) : periodicGrid L⊆periodicGrid M := by
  obtain ⟨m,rfl⟩:=h
  rintro ω ⟨hω,j,hj⟩
  refine ⟨hω,(m:ℤ)*j,?_⟩
  push_cast
  calc
    ((L:ℝ)*m)*(ω:ℝ)=(m:ℝ)*((L:ℝ)*(ω:ℝ)):=by ring
    _=(m:ℝ)*((j:ℝ)*(2*Real.pi)):=by rw [hj]
    _=((m:ℝ)*j)*(2*Real.pi):=by ring

theorem periodicFP_mono_dvd {Θ:Curve} {L M:ℕ} (h:L∣M) (hp:PeriodicFP Θ L) :
    PeriodicFP Θ M := by
  obtain ⟨w,hw,hcar⟩:=hp
  exact ⟨w,hw,hcar.mono (fun _ hω=>periodicGrid_mono_dvd h hω)⟩

theorem below_boundary_iff_sigma_pos (q:Tuning) :
    (q.kappa:EReal)<(Global.Threshold.kappaBoundary (Global.Threshold.parameters q)).val ↔
      0<Threshold.sigma q := by
  have hh:=Global.Threshold.kappaBoundary_le_iff (Global.Threshold.parameters q)
    (Global.Threshold.conditionNumber q)
  simp only [Global.Threshold.fixedThreshold,Global.Threshold.conditionNumber,Global.Threshold.sigma] at hh
  exact not_le.symm.trans ((not_congr hh).trans not_le)

theorem above_boundary_iff_sigma_neg (q:Tuning) :
    (Global.Threshold.kappaBoundary (Global.Threshold.parameters q)).val<(q.kappa:EReal) ↔
      Threshold.sigma q<0 := by
  have hh:=Global.Threshold.kappaBoundary_lt_iff (Global.Threshold.parameters q)
    (Global.Threshold.conditionNumber q)
  change _↔Threshold.sigma (Global.Threshold.tuning (Global.Threshold.parameters q)
    (Global.Threshold.conditionNumber q))<0 at hh
  rw [Global.Threshold.tuning_parameters] at hh
  exact hh

theorem on_boundary_iff_sigma_zero (q:Tuning) :
    (Global.Threshold.kappaBoundary (Global.Threshold.parameters q)).val=(q.kappa:EReal) ↔
      Threshold.sigma q=0 := by
  have hh:=Global.Threshold.kappaBoundary_eq_iff (Global.Threshold.parameters q)
    (Global.Threshold.conditionNumber q)
  change _↔Threshold.sigma (Global.Threshold.tuning (Global.Threshold.parameters q)
    (Global.Threshold.conditionNumber q))=0 at hh
  rw [Global.Threshold.tuning_parameters] at hh
  exact hh

theorem convergence_finite_witness (q:Tuning) (hs:0<Threshold.sigma q) :
    Nonempty (StrictSymbol (tuningCurve q) nonzeroLags) ∧ q.rate<1 := by
  have hn:¬FP (tuningCurve q):=by
    intro hp
    have hh:Threshold.sigma q≤0:=(Threshold.shifted_fp_iff q 0).mp (by
      simpa only [Geometry.shiftedCurve_zero] using hp)
    exact not_le_of_gt hs hh
  exact ⟨(infeasible_iff_strictSymbol _ _).mp hn,(rate_lt_one_iff_infeasible q).mpr hn⟩

theorem divergence_finite_witness (q:Tuning) (hs:Threshold.sigma q<0) :
    ∃L:ℕ,3≤L ∧ (∀m:ℕ,1≤m→PeriodicFP (tuningCurve q) (m*L)) ∧ 1≤q.rate := by
  obtain ⟨L,hL,hbound⟩:=Global.Threshold.periodic_approximation q 0 hs
  have hp:PeriodicFP (tuningCurve q) L:=by
    have hh:PeriodicFP (Geometry.shiftedCurve q 0) L:=
      (Threshold.shifted_periodic_iff q hL 0).mpr hbound.le
    simpa only [Geometry.shiftedCurve_zero] using hh
  exact ⟨L,hL,fun m _=>periodicFP_mono_dvd ⟨m,Nat.mul_comm _ _⟩ hp,
    fp_one_le_rate q hp.fp⟩

theorem boundary_rate {K:ℕ} {q:Tuning} (hq:q∈BoundaryInGap K) : 1≤q.rate:=
  fp_one_le_rate q (boundary_extremals_nonempty hq)

end polyak.ModeLocking
