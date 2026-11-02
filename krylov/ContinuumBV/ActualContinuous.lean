import krylov.ContinuumBV.ContinuousChain
import krylov.ContinuumBV.StringPath

/-!
Article: main_krylov, apC:lem:fund, continuous singular string states.
Use: derive continuity of the actual cumulative states on atom-free windows
and apply the proved nonlinear BV chain rule to their actual Bellman potential.
The mass may be singular continuous; no absolute-continuity assumption is made.
Source: actual Stieltjes atom updates and the continuous BV chain theorem.
-/

namespace krylov.ContinuumBV
noncomputable section
open Set Filter MeasureTheory
open krylov.Strings
open scoped Topology NNReal

/-- At a nonnegative point with no positive-position atom, the actual slope
is continuous. The distinguished unit atom at zero is already in the state. -/
theorem actual_slope_continuousAt (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1)
    {x : ℝ} (hx : 0 ≤ x) (hAtom : 0 < x → M.measure {x} = 0) :
    ContinuousAt (integralSlope M.measure φ) x := by
  apply (M.slope_monotone hc hm h₀).continuousAt_iff_leftLim_eq_rightLim.2
  rw [(M.slope_right_continuous hc x).rightLim_eq]
  by_cases hzero : x = 0
  · rw [hzero, M.slope_leftLim hc]
    simp [integralSlope]
  · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hzero)
    have hmass : M.measure.real {x} = 0 := by simp [Measure.real, hAtom hxp]
    have h := M.slope_atom_update hc hxp
    rw [hmass, zero_mul, add_zero] at h
    exact h.symm

/-- The energy has the same continuity property without smooth mass. -/
theorem actual_energy_continuousAt (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) {x : ℝ} (hx : 0 ≤ x)
    (hAtom : 0 < x → M.measure {x} = 0) :
    ContinuousAt (integralEnergy M.measure φ) x := by
  apply (M.energy_monotone hc).continuousAt_iff_leftLim_eq_rightLim.2
  rw [(M.energy_right_continuous hc x).rightLim_eq]
  by_cases hzero : x = 0
  · rw [hzero, M.energy_leftLim hc]
    simp [integralEnergy]
  · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hzero)
    have hmass : M.measure.real {x} = 0 := by simp [Measure.real, hAtom hxp]
    have h := M.energy_atom_update hc hxp
    rw [hmass, zero_mul, add_zero] at h
    exact h.symm

/-- Clipping an actual atom-free physical window gives a genuinely
continuous three-coordinate state path. -/
theorem continuous_clippedState_of_no_atoms (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1) (L : ℝ≥0)
    (hAtom : ∀ x ∈ Ioc 0 (L : ℝ), M.measure {x} = 0) :
    Continuous (clippedState M φ L) := by
  have hclip : Continuous (clipTime L) := continuous_subtype_val.comp continuous_projIcc
  have hp : Continuous (fun t => integralSlope M.measure φ (clipTime L t)) := by
    apply continuous_iff_continuousAt.2
    intro t
    have ht := (projIcc 0 (L : ℝ) L.property t).property
    exact (actual_slope_continuousAt M hc hm h₀ ht.1 (fun hpos => hAtom _ ⟨hpos, ht.2⟩)).comp
      (f := clipTime L) hclip.continuousAt
  have hK : Continuous (fun t => integralEnergy M.measure φ (clipTime L t)) := by
    apply continuous_iff_continuousAt.2
    intro t
    have ht := (projIcc 0 (L : ℝ) L.property t).property
    exact (actual_energy_continuousAt M hc ht.1 (fun hpos => hAtom _ ⟨hpos, ht.2⟩)).comp
      (f := clipTime L) hclip.continuousAt
  exact (hc.comp hclip).prodMk (hp.prodMk hK)

/-- Full nonlinear continuous-BV chain identity for the actual potential of
the actual measure-driven physical state, including singular continuous mass.
The graph differential equation is unnecessary for this calculus step. -/
theorem actual_continuous_potential_chain (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1) (L : ℝ≥0)
    (hAtom : ∀ x ∈ Ioc 0 (L : ℝ), M.measure {x} = 0)
    {γ : ℝ} {σ : ℝ → ℝ} (hγ : γ ≠ 0)
    (hσ : ∀ r, 1 ≤ r → ContDiffAt ℝ 1 σ r)
    (hσpos : ∀ r, 1 ≤ r → 0 < σ r) :
    let hz := boundedVariation_clippedState M hc hm h₀ L
    (∫ᵛ x in Ioc 0 (L : ℝ), fderiv ℝ (statePotential γ σ) (clippedState M φ L x)
      ∂[derivativePairing; hz.vectorMeasure]) =
        statePotential γ σ (clippedState M φ L L) -
          statePotential γ σ (clippedState M φ L 0) := by
  dsimp only
  apply continuous_chain_contDiff_compact
    (boundedVariation_clippedState M hc hm h₀ L)
    (continuous_clippedState_of_no_atoms M hc hm h₀ L hAtom)
    (isCompact_compactStateDomain M φ L) (fun t _ => clippedState_mem M hc hm h₀ L t)
    (s := compactStateDomain M φ L) (a := 0) (b := L)
  · intro w hw
    obtain ⟨hφ, hp, hK, hr⟩ := compactStateDomain_positive_ratio M φ L hw
    exact contDiffAt_statePotential hγ hφ.ne' hp.ne' hK.ne' (hσ _ hr) (hσpos _ hr)
  · exact L.property

end
end krylov.ContinuumBV
