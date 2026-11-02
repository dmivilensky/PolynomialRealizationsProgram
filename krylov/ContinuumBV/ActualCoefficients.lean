import krylov.ContinuumBV.ActualCadlag
import krylov.ContinuumBV.ActualContinuous
import krylov.ContinuumBV.ActualPhysical
import krylov.ContinuumBV.AtomicMeasure

/-!
Article: main_krylov, apC:eq:fundamental, identification of completed derivatives.
Use: off the actual atom set the averaged derivative is the ordinary state
derivative; at each atom its exact mass contribution is the nonlinear loss J.
Source: genuine one-sided state limits, atom updates and finite-chord FTC.
-/

namespace krylov.ContinuumBV
noncomputable section
open Set Filter MeasureTheory
open krylov.Strings krylov.ContinuumControl
open scoped Topology NNReal

/-- Off an actual positive-position atom the completed coefficient reduces
exactly to the usual Fréchet derivative of the actual post-state. -/
theorem actualChordCoefficient_of_no_atom (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1) (L : ℝ≥0)
    (γ : ℝ) (σ : ℝ → ℝ) {x : ℝ} (hx : x ∈ Ioc 0 (L : ℝ))
    (hAtom : M.measure {x} = 0) :
    actualChordCoefficient M γ σ φ L x = fderiv ℝ (statePotential γ σ) (clippedState M φ L x) := by
  have hp := actual_slope_continuousAt M hc hm h₀ hx.1.le (fun _ => hAtom)
  have hK := actual_energy_continuousAt M hc hx.1.le (fun _ => hAtom)
  have he : Function.leftLim (clippedState M φ L) x = clippedState M φ L x := by
    rw [clippedState_leftLim M hc hm h₀ L hx.1 hx.2,
      hp.continuousWithinAt.leftLim_eq, hK.continuousWithinAt.leftLim_eq]
    simp only [clippedState, clipTime_of_mem L (Ioc_subset_Icc_self hx)]
  rw [actualChordCoefficient, he, chordCoefficient_self]

/-- The actual drift coefficient off atoms is the derived positive drift
cost with its exact negative factor 1/2. -/
theorem actualChordCoefficient_drift_of_no_atom (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1) (L : ℝ≥0)
    {γ : ℝ} {σ : ℝ → ℝ} (hγ : γ ≠ 0)
    (hσ : ∀ r, 1 ≤ r → ContDiffAt ℝ 1 σ r)
    (hgraph : ∀ r, 1 ≤ r → FeedbackGraphAt γ σ r)
    {x : ℝ} (hx : x ∈ Ioc 0 (L : ℝ)) (hAtom : M.measure {x} = 0) :
    actualChordCoefficient M γ σ φ L x (driftDensity M φ x) = -1 / 2 * driftCost M γ σ φ x := by
  rw [actualChordCoefficient_of_no_atom M hc hm h₀ L γ σ hx hAtom]
  have hp := compactStateDomain_positive_ratio M φ L (clippedState_mem M hc hm h₀ L x)
  have hd := fderiv_statePotential_drift hγ hp.1 hp.2.1 hp.2.2.1
    (hσ _ hp.2.2.2) (hgraph _ hp.2.2.2)
  simp only [driftDirection, clippedState, clipTime_of_mem L (Ioc_subset_Icc_self hx),
    driftDensity, driftCost, mul_div_assoc] at hd ⊢
  linear_combination hd

/-- The ordinary mass coefficient is valid at every non-atomic point,
including points carrying singular continuous mass. -/
theorem actualChordCoefficient_mass_of_no_atom (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1) (L : ℝ≥0)
    {γ : ℝ} {σ : ℝ → ℝ} (hγ : γ ≠ 0)
    (hσ : ∀ r, 1 ≤ r → ContDiffAt ℝ 1 σ r)
    (hgraph : ∀ r, 1 ≤ r → FeedbackGraphAt γ σ r)
    {x : ℝ} (hx : x ∈ Ioc 0 (L : ℝ)) (hAtom : M.measure {x} = 0) :
    actualChordCoefficient M γ σ φ L x (massDensity φ x) = -1 / 2 * massCost M γ σ φ x := by
  rw [actualChordCoefficient_of_no_atom M hc hm h₀ L γ σ hx hAtom]
  have hp := compactStateDomain_positive_ratio M φ L (clippedState_mem M hc hm h₀ L x)
  have hd := fderiv_statePotential_mass hγ hp.1 hp.2.1 hp.2.2.1
    (hσ _ hp.2.2.2) (hgraph _ hp.2.2.2)
  simp only [massDirection, clippedState, clipTime_of_mem L (Ioc_subset_Icc_self hx),
    massDensity, massCost, massLossRate, mul_div_assoc] at hd ⊢
  linear_combination hd

/-- The contribution of every actual atom under the completed derivative is
its exact nonlinear potential jump, hence the negative of its true loss J. -/
theorem actualChordCoefficient_atom_mass (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1) (L : ℝ≥0)
    {γ : ℝ} {σ : ℝ → ℝ} (hγ : γ ≠ 0)
    (hσ : ∀ r, 1 ≤ r → ContDiffAt ℝ 1 σ r)
    (hgraph : ∀ r, 1 ≤ r → FeedbackGraphAt γ σ r)
    {x : ℝ} (hx : x ∈ Ioc 0 (L : ℝ)) :
    M.measure.real {x} * actualChordCoefficient M γ σ φ L x (massDensity φ x) =
      -actualAtomLoss M γ σ φ x := by
  have hdelta : clippedState M φ L x - Function.leftLim (clippedState M φ L) x =
      M.measure.real {x} • massDensity φ x := by
    rw [clippedState_leftLim M hc hm h₀ L hx.1 hx.2]
    simp only [clippedState, clipTime_of_mem L (Ioc_subset_Icc_self hx), massDensity]
    rw [M.slope_atom_update hc hx.1, M.energy_atom_update hc hx.1]
    ext <;> dsimp <;> ring
  have he := chordCoefficient_apply_sub (fun _ hw => actual_jump_chord_regular M hc hm h₀ L hγ hσ
    (fun r hr => (hgraph r hr).positive) hx hw)
  rw [hdelta, map_smul, smul_eq_mul] at he
  have hz := boundedVariation_clippedState M hc hm h₀ L
  have hreg : ∀ w ∈ segment ℝ (Function.leftLim (clippedState M φ L) x) (clippedState M φ L x),
      ContDiffAt ℝ 1 (statePotential γ σ) w := fun _ hw =>
    actual_jump_chord_regular M hc hm h₀ L hγ hσ (fun r hr => (hgraph r hr).positive) hx hw
  have hr := (clippedState_right_continuous M hc hm h₀ L (Ioc_subset_Icc_self hx)).rightLim_eq
  have hFr : ContinuousAt (statePotential γ σ) (Function.rightLim (clippedState M φ L) x) := by
    rw [hr]
    exact (hreg _ (right_mem_segment ℝ _ _)).continuousAt
  have hjump := actual_potential_jump M hc hm h₀ L hγ hσ hgraph hx
  rw [rightLim_comp hz hFr, leftLim_comp hz (hreg _ (left_mem_segment ℝ _ _)).continuousAt, hr] at hjump
  exact he.trans hjump

/-- Countability makes the true atom set null for physical length. -/
theorem volume_ae_not_massAtomSet (M : Mass) : ∀ᵐ x ∂volume, x ∉ massAtomSet M := by
  apply ae_iff.2
  have he : {x : ℝ | ¬x ∉ massAtomSet M} = massAtomSet M := by ext; simp
  rw [he]
  exact (massAtomSet_countable M).measure_zero volume

/-- The canonical continuous singular component is supported off every
actual atom, without any unproved nonatomicity assumption. -/
theorem continuousSingularMass_ae_not_massAtomSet (M : Mass) :
    ∀ᵐ x ∂continuousSingularMass M, x ∉ massAtomSet M :=
  ae_restrict_mem (massAtomSet_countable M).measurableSet.compl

end
end krylov.ContinuumBV
