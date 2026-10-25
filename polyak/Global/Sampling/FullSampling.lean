import polyak.Global.Sampling.FullSamplingCore
import polyak.Global.Sampling.Eventual

/-! The full sampling theorem and its global consequences. The analytic
sampler is the actual smoothing, Fourier decay, and aliasing construction. -/
noncomputable section
namespace polyak.Global.Sampling
open General Levels MeasureTheory Set

theorem actual_periodic_sampler : PeriodicSampler := by
  intro q s w hw hm hl
  exact eventually_periodic_of_strict_solution q s hw hm hl

theorem eventual_periodic_after_shift (q : Tuning) (s : ℝ)
    {ν : Measure Frequency} (hν : Levels.Threshold.MonotoneSolution
      (Levels.Threshold.shiftedCotangent q s) ν) (hNP : Nonperiodic ν)
    {ε : ℝ} (hε : 0<ε) :
    ∃L0 : ℕ,∀L≥L0,PeriodicFP (Geometry.shiftedCurve q (s+ε)) L := by
  obtain ⟨w,hw,_,hm,hl⟩ := strict_measure_after_shift q s hν hNP hε
  exact actual_periodic_sampler q (s+ε) w hw hm hl

theorem sigmaPeriodic_eq_sigma_of_carried (q : Tuning) {k : ℕ} (hk : 3≤k)
    {ν : Measure Frequency} (hν : Levels.Threshold.MonotoneSolution
      (Levels.Threshold.shiftedCotangent q (Levels.Threshold.sigma q)) ν)
    (hcar : ∀ᵐω∂ν,ω∈periodicGrid k) :
    Levels.Threshold.sigmaPeriodic q k=Levels.Threshold.sigma q := by
  apply le_antisymm
  · apply (Levels.Threshold.shifted_periodic_iff q hk _).mp
    exact (Levels.Threshold.shifted_monoform_carried_iff q _ (periodicGrid k)).mpr ⟨ν,hν,hcar⟩
  · exact Levels.Threshold.sigma_le_sigmaPeriodic q hk

theorem eventual_sigmaPeriodic_le_add_of_nonperiodic (q : Tuning)
    {ν : Measure Frequency} (hν : Levels.Threshold.MonotoneSolution
      (Levels.Threshold.shiftedCotangent q (Levels.Threshold.sigma q)) ν)
    (hNP : Nonperiodic ν) {ε : ℝ} (hε : 0<ε) :
    ∃L0 : ℕ,3≤L0 ∧ ∀L≥L0,
      Levels.Threshold.sigmaPeriodic q L≤Levels.Threshold.sigma q+ε := by
  obtain ⟨L0,hL0⟩ := eventual_periodic_after_shift q _ hν hNP hε
  refine ⟨max L0 3,le_max_right _ _,?_⟩
  intro L hL
  have hL3 : 3≤L := (le_max_right L0 3).trans hL
  exact (Levels.Threshold.shifted_periodic_iff q hL3 _).mp
    (hL0 L ((le_max_left L0 3).trans hL))

theorem eventual_periodic_after_kappa (q p : Tuning)
    (hy : p.y=q.y) (hb : p.beta=q.beta) (hκ : q.kappa<p.kappa) (s : ℝ)
    {ν : Measure Frequency} (hν : Levels.Threshold.MonotoneSolution
      (Levels.Threshold.shiftedCotangent q s) ν) (hNP : Nonperiodic ν) :
    ∃L0 : ℕ,∀L≥L0,PeriodicFP (Geometry.shiftedCurve p s) L :=
  eventual_periodic_after_kappa_core actual_periodic_sampler q p hy hb hκ s hν hNP

theorem periodic_alternative (q : Tuning) (hq : q∈Regions.divergenceSet) :
    (∃k : ℕ,3≤k ∧ PeriodicFP (tuningCurve q) k ∧
      ∀p : Tuning,p.y=q.y→p.beta=q.beta→q.kappa≤p.kappa→PeriodicFP (tuningCurve p) k) ∨
    (∀p : Tuning,p.y=q.y→p.beta=q.beta→q.kappa<p.kappa→
      ∃L0 : ℕ,∀L≥L0,PeriodicFP (tuningCurve p) L) :=
  periodic_alternative_core actual_periodic_sampler q hq

theorem periodic_threshold_approximation (q : Tuning) {ε : ℝ} (hε : 0<ε) :
    ∃L : ℕ,3≤L ∧ Levels.Threshold.sigmaPeriodic q L≤Levels.Threshold.sigma q+ε :=
  periodic_threshold_approximation_core actual_periodic_sampler q hε

theorem sigma_eq_iInf_sigmaPeriodic (q : Tuning) :
    Levels.Threshold.sigma q=⨅k : Set.Ici (3:ℕ),Levels.Threshold.sigmaPeriodic q k.val :=
  sigma_eq_iInf_sigmaPeriodic_core actual_periodic_sampler q

theorem divergence_eq_closure_periodicUnion :
    Regions.divergenceSet=closure periodicUnion :=
  divergence_eq_closure_periodicUnion_core actual_periodic_sampler

end polyak.Global.Sampling
