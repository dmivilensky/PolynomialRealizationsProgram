import polyak.Global.Sampling.ProfileGap
import polyak.Levels.Realization.ThresholdSets
import Mathlib.Analysis.SpecificLimits.Basic

/-! Consequences of the all-large-period sampling theorem. The final
wrapper supplies its actual analytic proof, not a user hypothesis. -/
noncomputable section
namespace polyak.Global.Sampling
open General Levels MeasureTheory Filter Set Topology

 def PeriodicSampler : Prop := ∀(q : Tuning)(s : ℝ)(w : Measure Frequency),
  ProgramSolution (Geometry.shiftedCurve q s) nonzeroLags w→
  (0<∫ω,(Geometry.shiftedCurve q s).minimizer ω∂w)→
  (∀n : ℤ,n≠0→0<∫ω,(Geometry.shiftedCurve q s).lag n ω∂w)→
  ∃L0 : ℕ,∀L≥L0,PeriodicFP (Geometry.shiftedCurve q s) L

 theorem eventual_periodic_after_kappa_core (sample : PeriodicSampler) (q p : Tuning)
    (hy : p.y=q.y) (hb : p.beta=q.beta) (hκ : q.kappa<p.kappa) (s : ℝ)
    {ν : Measure Frequency} (hν : Levels.Threshold.MonotoneSolution
      (Levels.Threshold.shiftedCotangent q s) ν) (hNP : Nonperiodic ν) :
    ∃L0 : ℕ,∀L≥L0,PeriodicFP (Geometry.shiftedCurve p s) L := by
  obtain ⟨w,hw,_,hm,hl⟩ := strict_measure_after_kappa q p hy hb hκ s hν hNP
  exact sample p s w hw hm hl

 theorem periodic_alternative_core (sample : PeriodicSampler) (q : Tuning)
    (hq : q∈Regions.divergenceSet) :
    (∃k : ℕ,3≤k ∧ PeriodicFP (tuningCurve q) k ∧
      ∀p : Tuning,p.y=q.y→p.beta=q.beta→q.kappa≤p.kappa→PeriodicFP (tuningCurve p) k) ∨
    (∀p : Tuning,p.y=q.y→p.beta=q.beta→q.kappa<p.kappa→
      ∃L0 : ℕ,∀L≥L0,PeriodicFP (tuningCurve p) L) := by
  by_cases hperiod : ∃k : ℕ,3≤k ∧ PeriodicFP (tuningCurve q) k
  · obtain ⟨k,hk,hqk⟩ := hperiod
    refine Or.inl ⟨k,hk,hqk,?_⟩
    intro p hy hb hκ
    have hp := periodic_kappa_mono q p hy hb hκ 0
      (by simpa only [Geometry.shiftedCurve_zero] using hqk)
    simpa only [PeriodicFP,Geometry.shiftedCurve_zero] using hp
  · right
    have hFP : FP (Geometry.shiftedCurve q 0) := by
      rw [Geometry.shiftedCurve_zero]
      exact (divergenceSet_iff_fp q).mp hq
    obtain ⟨ν,hν⟩ := (Levels.Threshold.shifted_monoform_iff q 0).mp hFP
    have hNP : Nonperiodic ν := by
      intro k hk hcar
      apply hperiod
      refine ⟨k,hk,?_⟩
      have hp := (Levels.Threshold.shifted_monoform_carried_iff q 0 (periodicGrid k)).mpr ⟨ν,hν,hcar⟩
      simpa only [PeriodicFP,Geometry.shiftedCurve_zero] using hp
    intro p hy hb hκ
    obtain ⟨L0,hL0⟩ := eventual_periodic_after_kappa_core sample q p hy hb hκ 0 hν hNP
    exact ⟨L0,fun L hL=>by simpa only [Geometry.shiftedCurve_zero] using hL0 L hL⟩

 theorem periodic_threshold_approximation_core (sample : PeriodicSampler) (q : Tuning)
    {ε : ℝ} (hε : 0<ε) :
    ∃L : ℕ,3≤L ∧ Levels.Threshold.sigmaPeriodic q L≤Levels.Threshold.sigma q+ε := by
  let s := Levels.Threshold.sigma q
  obtain ⟨ν,hν⟩ := (Levels.Threshold.shifted_monoform_iff q s).mp
    (Levels.Threshold.sigma_feasible q)
  by_cases hp : ∃k : ℕ,3≤k ∧ ∀ᵐω∂ν,ω∈periodicGrid k
  · obtain ⟨k,hk,hcar⟩ := hp
    have hpk : PeriodicFP (Geometry.shiftedCurve q s) k :=
      (Levels.Threshold.shifted_monoform_carried_iff q s (periodicGrid k)).mpr ⟨ν,hν,hcar⟩
    have hs := (Levels.Threshold.shifted_periodic_iff q hk s).mp hpk
    exact ⟨k,hk,by dsimp only [s] at hs;linarith⟩
  · have hNP : Nonperiodic ν := fun k hk hcar=>hp ⟨k,hk,hcar⟩
    obtain ⟨w,hw,_,hm,hl⟩ := strict_measure_after_shift q s hν hNP hε
    obtain ⟨L0,hL0⟩ := sample q (s+ε) w hw hm hl
    let L := max L0 3
    have hL : 3≤L := le_max_right _ _
    have hpL := hL0 L (le_max_left _ _)
    exact ⟨L,hL,(Levels.Threshold.shifted_periodic_iff q hL (s+ε)).mp hpL⟩

 theorem sigma_eq_iInf_sigmaPeriodic_core (sample : PeriodicSampler) (q : Tuning) :
    Levels.Threshold.sigma q=⨅k : Set.Ici (3:ℕ),Levels.Threshold.sigmaPeriodic q k.val := by
  let V : Set ℝ := range (fun k : Set.Ici (3:ℕ)=>Levels.Threshold.sigmaPeriodic q k.val)
  have hne : V.Nonempty := ⟨_,⟨⟨3,by norm_num⟩,rfl⟩⟩
  have hlow : ∀v∈V,Levels.Threshold.sigma q≤v := by
    rintro v ⟨k,rfl⟩
    exact Levels.Threshold.sigma_le_sigmaPeriodic q k.property
  have hbd : BddBelow V := ⟨Levels.Threshold.sigma q,hlow⟩
  change Levels.Threshold.sigma q=sInf V
  apply le_antisymm (le_csInf hne hlow)
  by_contra hh
  have hg : Levels.Threshold.sigma q<sInf V := lt_of_not_ge hh
  let ε := (sInf V-Levels.Threshold.sigma q)/2
  have hε : 0<ε := by dsimp [ε];linarith
  obtain ⟨L,hL,hbound⟩ := periodic_threshold_approximation_core sample q hε
  have hmem : Levels.Threshold.sigmaPeriodic q L∈V := ⟨⟨L,hL⟩,rfl⟩
  have hb := csInf_le hbd hmem
  dsimp [ε] at hbound
  linarith

 def periodicUnion : Set Tuning := {q|∃k : ℕ,3≤k ∧ PeriodicFP (tuningCurve q) k}

 theorem periodicUnion_subset_divergence : periodicUnion⊆Regions.divergenceSet := by
  rintro q ⟨_,_,h⟩
  exact periodicFP_diverges q h

 theorem isClosed_divergenceSet : IsClosed Regions.divergenceSet := by
  have hc := Levels.Threshold.isClosed_sigma_epigraph.preimage
    (continuous_id.prodMk (show Continuous (fun _ : Tuning=>(0:ℝ)) from continuous_const))
  have he : Regions.divergenceSet={q : Tuning|Levels.Threshold.sigma q≤0} := by
    ext q
    exact divergenceSet_iff_sigma_nonpos q
  rw [he]
  exact hc

 def raiseKappa (q : Tuning) (j : ℕ) : Tuning where
  kappa := q.kappa+1/((j:ℝ)+1)
  y := q.y
  beta := q.beta
  kappa_gt_one := by
    have h : 0<1/((j:ℝ)+1) := by positivity
    linarith [q.kappa_gt_one]
  beta_nonneg := q.beta_nonneg
  beta_lt_one := q.beta_lt_one
  y_pos := q.y_pos
  y_lt := q.y_lt

 theorem raiseKappa_strict (q : Tuning) (j : ℕ) : q.kappa<(raiseKappa q j).kappa := by
  change q.kappa<q.kappa+1/((j:ℝ)+1)
  have h : 0<1/((j:ℝ)+1) := by positivity
  linarith

 theorem raiseKappa_tendsto (q : Tuning) : Tendsto (raiseKappa q) atTop (𝓝 q) := by
  rw [show (𝓝 q)=Filter.comap (fun p : Tuning=>(p.kappa,p.y,p.beta))
    (𝓝 (q.kappa,q.y,q.beta)) from nhds_induced _ _]
  apply tendsto_comap_iff.mpr
  have hi : Tendsto (fun j : ℕ=>1/((j:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hκ : Tendsto (fun j : ℕ=>q.kappa+1/((j:ℝ)+1)) atTop (𝓝 q.kappa) := by
    simpa only [add_zero] using (tendsto_const_nhds (x:=q.kappa)).add hi
  have hy : Tendsto (fun _ : ℕ=>q.y) atTop (𝓝 q.y) := tendsto_const_nhds
  have hb : Tendsto (fun _ : ℕ=>q.beta) atTop (𝓝 q.beta) := tendsto_const_nhds
  exact hκ.prodMk_nhds (hy.prodMk_nhds hb)

 theorem divergence_eq_closure_periodicUnion_core (sample : PeriodicSampler) :
    Regions.divergenceSet=closure periodicUnion := by
  apply subset_antisymm
  · intro q hq
    have hp : ∀j : ℕ,raiseKappa q j∈periodicUnion := by
      intro j
      rcases periodic_alternative_core sample q hq with ⟨k,hk,_,hmono⟩|hall
      · exact ⟨k,hk,hmono _ rfl rfl (raiseKappa_strict q j).le⟩
      · obtain ⟨L0,hL0⟩ := hall (raiseKappa q j) rfl rfl (raiseKappa_strict q j)
        exact ⟨max L0 3,le_max_right _ _,hL0 _ (le_max_left _ _)⟩
    exact mem_closure_of_tendsto (raiseKappa_tendsto q) (Eventually.of_forall hp)
  · exact closure_minimal periodicUnion_subset_divergence isClosed_divergenceSet

end polyak.Global.Sampling
