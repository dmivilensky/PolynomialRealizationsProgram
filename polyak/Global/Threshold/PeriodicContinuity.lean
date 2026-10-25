import polyak.Levels.Threshold.PeriodicThreshold
import Mathlib.Topology.Semicontinuity.Basic

/-! Continuity of every actual finite periodic threshold. A fixed feasible
measure is retained under perturbation: the finitely many grid values of
the monotone profile are dominated after an arbitrarily small shift. This
preserves every lag class, including those identically zero on its support. -/
noncomputable section
namespace polyak.Global.Threshold
open General Levels Set Filter MeasureTheory
open scoped Topology

abbrev sigma := Levels.Threshold.sigma
abbrev sigmaPeriodic := Levels.Threshold.sigmaPeriodic

theorem continuous_cotangent_at_frequency (ω : Frequency) :
    Continuous (fun q : Tuning=>Geometry.cotangent q ω) := by
  change Continuous (fun q : Tuning=>q.Xi (Real.cos ω)/Real.sin ω)
  simpa only [Function.comp_def,Chart.eval_coefficients] using
    ((Chart.Coefficients.continuous_eval (Real.cos ω)).comp Chart.continuous_coefficients).div_const (Real.sin ω)

theorem periodic_compare_on_grid {q p : Tuning} {k : ℕ} {s t : ℝ}
    (horder : ∀ω∈periodicGrid k,Geometry.cotangent q ω+s≤Geometry.cotangent p ω+t)
    (hs : PeriodicFP (Geometry.shiftedCurve q s) k) :
    PeriodicFP (Geometry.shiftedCurve p t) k := by
  obtain ⟨ν,hν,hcar⟩:=(Levels.Threshold.shifted_monoform_carried_iff q s (periodicGrid k)).mp hs
  have hm : Measurable (Levels.Threshold.shiftedCotangent p t) := by
    unfold Levels.Threshold.shiftedCotangent Geometry.cotangent Tuning.Xi
    fun_prop
  have hle : ∀ᵐω∂ν,Levels.Threshold.shiftedCotangent q s ω≤Levels.Threshold.shiftedCotangent p t ω :=
    hcar.mono fun ω hω=>horder ω hω
  have hbound : ∀ᵐω∂ν,Levels.Threshold.shiftedCotangent p t ω≤Geometry.cotangentUpper p+t :=
    hν.2.2.1.mono fun ω hω=>by
      dsimp [Levels.Threshold.shiftedCotangent]
      linarith [Geometry.cotangent_le_upper p hω]
  exact (Levels.Threshold.shifted_monoform_carried_iff p t (periodicGrid k)).mpr
    ⟨ν,(hν.mono_ae hm.aestronglyMeasurable hle hbound).1,hcar⟩

theorem eventually_sigmaPeriodic_le_add (q : Tuning) {k : ℕ} (hk : 3≤k)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠp : Tuning in 𝓝 q,sigmaPeriodic p k≤sigmaPeriodic q k+ε := by
  have hnear : ∀ᶠp : Tuning in 𝓝 q,
      ∀ω∈periodicGrid k,Geometry.cotangent q ω<Geometry.cotangent p ω+ε := by
    apply (periodicGrid_finite (by omega : 0<k)).eventually_all.mpr
    intro ω _
    exact ((continuous_cotangent_at_frequency ω).add_const ε).continuousAt.eventually
      (eventually_gt_nhds (by linarith : Geometry.cotangent q ω<Geometry.cotangent q ω+ε))
  filter_upwards [hnear] with p hp
  apply (Levels.Threshold.shifted_periodic_iff p hk _).mp
  apply periodic_compare_on_grid (hs:=Levels.Threshold.sigmaPeriodic_feasible q hk)
  intro ω hω
  linarith [hp ω hω]

theorem upperSemicontinuous_sigmaPeriodic {k : ℕ} (hk : 3≤k) :
    UpperSemicontinuous (fun q : Tuning=>sigmaPeriodic q k) := by
  intro q a ha
  have hε : 0<(a-sigmaPeriodic q k)/2:=by linarith
  filter_upwards [eventually_sigmaPeriodic_le_add q hk hε] with p hp
  linarith

theorem lowerSemicontinuous_sigmaPeriodic {k : ℕ} (hk : 3≤k) :
    LowerSemicontinuous (fun q : Tuning=>sigmaPeriodic q k) :=
  lowerSemicontinuous_iff_isClosed_epigraph.mpr (Levels.Threshold.isClosed_sigmaPeriodic_epigraph hk)

theorem continuous_sigmaPeriodic {k : ℕ} (hk : 3≤k) :
    Continuous (fun q : Tuning=>sigmaPeriodic q k) :=
  continuous_iff_lower_upperSemicontinuous.mpr
    ⟨lowerSemicontinuous_sigmaPeriodic hk,upperSemicontinuous_sigmaPeriodic hk⟩

theorem lowerSemicontinuous_sigma : LowerSemicontinuous sigma :=
  lowerSemicontinuous_iff_isClosed_epigraph.mpr Levels.Threshold.isClosed_sigma_epigraph

/-- The analytic topological part of global(a); its premise is discharged
by the actual periodic sampling theorem in the final source wrapper. -/
theorem continuous_sigma_of_periodic_approximation
    (happrox : ∀q : Tuning,∀s : ℝ,sigma q<s→∃k : ℕ,3≤k ∧ sigmaPeriodic q k<s) :
    Continuous sigma := by
  refine continuous_iff_lower_upperSemicontinuous.mpr ⟨lowerSemicontinuous_sigma,?_⟩
  intro q s hs
  obtain ⟨k,hk,hks⟩:=happrox q s hs
  have he : ∀ᶠp : Tuning in 𝓝 q,sigmaPeriodic p k<s:=
    (upperSemicontinuous_sigmaPeriodic hk) q s hks
  filter_upwards [he] with p hp
  exact (Levels.Threshold.sigma_le_sigmaPeriodic p hk).trans_lt hp

end polyak.Global.Threshold
