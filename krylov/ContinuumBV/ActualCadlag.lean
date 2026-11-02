import krylov.ContinuumBV.CadlagPhysical
import krylov.ContinuumBV.ChordDomain
import krylov.ContinuumBV.EqualGrid
import krylov.ContinuumBV.StateIncrements

/-!
Article: main_krylov, apC:lem:fund, arbitrary physical mass.
Use: construct all C¹ chord partitions from the actual admissible state, even
with infinitely many atoms. Only φ is used as a continuous coordinate; slope
and energy retain their true jumps. The nonlinear invariant is localized by
its explicitly proved quadratic chord defect.
Source: actual state positivity/BV, Heine–Cantor, and graph-completed BV calculus.
-/

namespace krylov.ContinuumBV
noncomputable section
open Set Filter MeasureTheory
open krylov.Strings krylov.ContinuumControl
open scoped Topology NNReal

/-- The actual clipped BV state is right continuous, including atoms at the
right endpoint. No atom-free or absolutely continuous mass assumption occurs. -/
theorem clippedState_right_continuous (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1) (L : ℝ≥0)
    {x : ℝ} (hx : x ∈ Icc 0 (L : ℝ)) :
    ContinuousWithinAt (clippedState M φ L) (Ici x) x := by
  apply continuousWithinAt_Ioi_iff_Ici.1
  have he : Function.rightLim (clippedState M φ L) x = clippedState M φ L x := by
    rw [clippedState_rightLim M hc L hx]
    simp only [clippedState, clipTime_of_mem L hx]
  change Tendsto _ _ _
  rw [← he]
  exact (boundedVariation_clippedState M hc hm h₀ L).tendsto_rightLim x

/-- C¹ regularity holds on the whole true jump chord, because φ has the same
left and post-state value and the invariant domain is convex on that slice. -/
theorem actual_jump_chord_regular (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1) (L : ℝ≥0)
    {γ : ℝ} {σ : ℝ → ℝ} (hγ : γ ≠ 0)
    (hσ : ∀ r, 1 ≤ r → ContDiffAt ℝ 1 σ r) (hσpos : ∀ r, 1 ≤ r → 0 < σ r)
    {x : ℝ} (hx : x ∈ Ioc 0 (L : ℝ))
    {w : PotentialState} (hw : w ∈ segment ℝ (Function.leftLim (clippedState M φ L) x)
      (clippedState M φ L x)) : ContDiffAt ℝ 1 (statePotential γ σ) w := by
  have hz := boundedVariation_clippedState M hc hm h₀ L
  have hu := leftLim_mem_of_closed hz (isCompact_compactStateDomain M φ L).isClosed
    (fun x _ => clippedState_mem M hc hm h₀ L x) x
  have hv := clippedState_mem M hc hm h₀ L x
  have heq : (Function.leftLim (clippedState M φ L) x).1 = (clippedState M φ L x).1 := by
    rw [clippedState_leftLim M hc hm h₀ L hx.1 hx.2]
    simp only [clippedState, clipTime_of_mem L (Ioc_subset_Icc_self hx)]
  have hdom := chord_mem_compactStateDomain_of_first_eq M φ L hu hv heq hw
  obtain ⟨hφ, hp, hK, hr⟩ := compactStateDomain_positive_ratio M φ L hdom
  exact contDiffAt_statePotential hγ hφ.ne' hp.ne' hK.ne' (hσ _ hr) (hσpos _ hr)

/-- Actual refining time partitions with all their C¹ chord bounds derived.
No regularity or nonlinear identity is assumed for discontinuous state paths. -/
def actual_chordPartitions (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1) (L : ℝ≥0)
    {γ : ℝ} {σ : ℝ → ℝ} (hγ : γ ≠ 0)
    (hσ : ∀ r, 1 ≤ r → ContDiffAt ℝ 1 σ r) (hσpos : ∀ r, 1 ≤ r → 0 < σ r) :
    C1ChordPartitions (clippedState M φ L) (statePotential γ σ) 0 L := Classical.choice (by
  have hreg : ∀ w ∈ compactStateDomain M φ L, ContDiffAt ℝ 1 (statePotential γ σ) w := by
    intro w hw
    obtain ⟨hφ, hp, hK, hr⟩ := compactStateDomain_positive_ratio M φ L hw
    exact contDiffAt_statePotential hγ hφ.ne' hp.ne' hK.ne' (hσ _ hr) (hσpos _ hr)
  obtain ⟨η, hη, C, hnear⟩ := exists_uniform_contDiff_neighborhood
    (isCompact_compactStateDomain M φ L) hreg
  let P := integralSlope M.measure φ L + 1
  have hP : 0 < P := by dsimp [P]; linarith [M.slope_one_le hm h₀ (L : ℝ)]
  obtain ⟨δ, hδ, htime⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hc.continuousOn) (η / P) (div_pos hη hP)
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hε : ∀ k, 0 < ε k := by intro k; dsimp [ε]; positivity
  choose N hN ht ha hb hmem hmesh using fun k => exists_equalGrid L.property (lt_min hδ (hε k))
  let t : ℕ → ℕ → ℝ := fun k => equalGrid 0 (L : ℝ) (N k)
  have hchord : ∀ k i, i < N k → ∀ w ∈ segment ℝ
      (clippedState M φ L (t k i)) (clippedState M φ L (t k (i + 1))),
      ContDiffAt ℝ 1 (statePotential γ σ) w ∧ ‖fderiv ℝ (statePotential γ σ) w‖ ≤ C := by
    intro k i hi w hw
    have hui : t k i ∈ Icc 0 (L : ℝ) := hmem k i
    have hvi : t k (i + 1) ∈ Icc 0 (L : ℝ) := hmem k (i + 1)
    have huv : t k i ≤ t k (i + 1) := ht k (Nat.le_succ i)
    have hu := clippedState_mem M hc hm h₀ L (t k i)
    have hv := clippedState_mem M hc hm h₀ L (t k (i + 1))
    have hφord : (clippedState M φ L (t k i)).1 ≤ (clippedState M φ L (t k (i + 1))).1 := by
      simpa only [clippedState, clipTime_of_mem L hui, clipTime_of_mem L hvi] using hm huv
    have hpord : (clippedState M φ L (t k i)).2.1 ≤ (clippedState M φ L (t k (i + 1))).2.1 := by
      simpa only [clippedState, clipTime_of_mem L hui, clipTime_of_mem L hvi] using
        M.slope_monotone hc hm h₀ huv
    obtain ⟨q, hq, hqbound⟩ := chord_near_compactStateDomain M φ L hu hv hφord hpord hw
    have hdist : dist (t k (i + 1)) (t k i) < δ := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 huv)]
      exact (hmesh k i hi).trans_le (min_le_left _ _)
    have hφclose : (clippedState M φ L (t k (i + 1))).1 - (clippedState M φ L (t k i)).1 < η / P := by
      have he := htime (t k (i + 1)) hvi (t k i) hui hdist
      simpa only [clippedState, clipTime_of_mem L hui, clipTime_of_mem L hvi,
        Real.dist_eq, abs_of_nonneg (sub_nonneg.2 (hm huv))] using he
    have hpbound : (clippedState M φ L (t k (i + 1))).2.1 -
        (clippedState M φ L (t k i)).2.1 ≤ P := by
      dsimp [P]
      linarith [hv.1.2.1.2, hu.1.2.1.1]
    apply hnear q hq w
    exact hqbound.trans_lt ((mul_le_mul_of_nonneg_left hpbound (sub_nonneg.2 hφord)).trans_lt
      ((lt_div_iff₀ hP).1 hφclose))
  exact ⟨{
    time := t
    size := N
    tolerance := ε
    monotone := ht
    initial := ha
    terminal := hb
    mesh := fun k i hi => (hmesh k i hi).le.trans (min_le_right _ _)
    tendsto_tolerance := tendsto_one_div_add_atTop_nhds_zero_nat
    regular := fun k i hi w hw => (hchord k i hi w hw).1
    bounded := ⟨C, fun k i hi w hw => (hchord k i hi w hw).2⟩ }⟩)

/-- The genuine graph-completed derivative coefficient at an actual state.
At an atom it averages along the complete pre/post-state chord. -/
def actualChordCoefficient (M : Mass) (γ : ℝ) (σ φ : ℝ → ℝ) (L : ℝ≥0) (x : ℝ) :
    PotentialState →L[ℝ] ℝ :=
  chordCoefficient (statePotential γ σ) (Function.leftLim (clippedState M φ L) x)
    (clippedState M φ L x)

/-- Every genuine integrable physical state density has an integrable action
under the completed derivative; countable atoms are explicitly allowed. -/
theorem actualChordCoefficient_action_integrable (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1) (L : ℝ≥0)
    {γ : ℝ} {σ : ℝ → ℝ} (hγ : γ ≠ 0)
    (hσ : ∀ r, 1 ≤ r → ContDiffAt ℝ 1 σ r) (hσpos : ∀ r, 1 ≤ r → 0 < σ r)
    {μ : Measure ℝ} {h : ℝ → PotentialState}
    (hs : ∀ᵐ x ∂μ, x ∈ Ioc 0 (L : ℝ)) (hi : Integrable h μ) :
    Integrable (fun x => actualChordCoefficient M γ σ φ L x (h x)) μ :=
  (actual_chordPartitions M hc hm h₀ L hγ hσ hσpos).action_integrable
    (boundedVariation_clippedState M hc hm h₀ L)
    (fun _ hx => clippedState_right_continuous M hc hm h₀ L hx)
    (fun _ hx _ hw => actual_jump_chord_regular M hc hm h₀ L hγ hσ hσpos hx hw) hs hi

/-- Exact physical chain identity for the actual state with arbitrary atoms
and singular continuous mass. All partitions and derivative bounds are
constructed from the source hypotheses; no chain certificate is supplied. -/
theorem actual_cadlag_physical_identity (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1) (L : ℝ≥0)
    (he : ∀ x ∈ Icc 0 (L : ℝ), φ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure φ t)
    {γ : ℝ} {σ : ℝ → ℝ} (hγ : γ ≠ 0)
    (hσ : ∀ r, 1 ≤ r → ContDiffAt ℝ 1 σ r) (hσpos : ∀ r, 1 ≤ r → 0 < σ r) :
    (∫ x in Ioc 0 (L : ℝ), actualChordCoefficient M γ σ φ L x (driftDensity M φ x)) +
      (∫ x in Ioc 0 (L : ℝ), actualChordCoefficient M γ σ φ L x (massDensity φ x) ∂M.measure) =
        statePotential γ σ (clippedState M φ L L) - statePotential γ σ (clippedState M φ L 0) := by
  let p := actual_chordPartitions M hc hm h₀ L hγ hσ hσpos
  have hinc : ∀ u v, u ∈ Icc 0 (L : ℝ) → v ∈ Icc 0 (L : ℝ) → u ≤ v →
      clippedState M φ L v - clippedState M φ L u =
        (∫ x in Ioc u v, driftDensity M φ x ∂volume.restrict (Ioc 0 (L : ℝ))) +
          (∫ x in Ioc u v, massDensity φ x ∂M.measure.restrict (Ioc 0 (L : ℝ))) := by
    intro u v hu hv huv
    have hsub : Ioc u v ⊆ Ioc (0 : ℝ) L := Ioc_subset_Ioc hu.1 hv.2
    simpa only [Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.2 hsub,
      clippedState, clipTime_of_mem L hu, clipTime_of_mem L hv, rawState] using
      rawState_increment M hc hm h₀ L he hu hv huv
  exact cadlag_physical_chain_of_partitions (boundedVariation_clippedState M hc hm h₀ L)
    p.time p.size p.tolerance p.monotone p.initial p.terminal p.mesh p.tendsto_tolerance
    (fun _ hx => clippedState_right_continuous M hc hm h₀ L hx)
    p.regular (fun _ hx _ hw => actual_jump_chord_regular M hc hm h₀ L hγ hσ hσpos hx hw) p.bounded
    (volume.restrict (Ioc 0 (L : ℝ))) (M.measure.restrict (Ioc 0 (L : ℝ)))
    (driftDensity M φ) (massDensity φ)
    (ae_restrict_mem measurableSet_Ioc) (ae_restrict_mem measurableSet_Ioc)
    (driftDensity_integrable M hc hm h₀ 0 L) (massDensity_integrable M hc 0 L) hinc

end
end krylov.ContinuumBV
