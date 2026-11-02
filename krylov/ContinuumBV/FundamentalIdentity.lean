import krylov.ContinuumBV.ActualCoefficients
import krylov.ContinuumBV.SingularIdentity

/-!
Article: main_krylov, apC:eq:fundamental and apC:lem:fund.
Use: the full fundamental identity for the actual physical string, with
arbitrary singular continuous mass and countably many nonlinear atoms. The
distinguished origin atom is already in the initial state and is excluded
from the loss sum. All finite-window cost integrability is proved.
Source: the actual graph-completed BV chain, Lebesgue decomposition, exact
singleton losses and mathlib's countable-set Bochner integration theorem.
-/

/-!
Article: krylov, Lemma D.13 [apC:lem:fund].

The actual cadlag state potential loses exactly reward, square loss, continuous singular loss
and a convergent sum of positive atom losses.
The origin atom is excluded from the jump sum because it already enters the initial state;
general finite endpoints are reduced to compact windows.
-/

namespace krylov.ContinuumBV
noncomputable section
open Set Filter MeasureTheory
open krylov.Strings krylov.ContinuumControl
open scoped Topology NNReal

/-- Full actual physical cost identity before square completion. The three
continuous costs are genuinely integrable, and every positive-position atom
contributes its exact nonlinear loss rather than a linearized mass cost. -/
theorem actual_cadlag_cost_identity (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1) (L : ℝ≥0)
    (he : ∀ x ∈ Icc 0 (L : ℝ), φ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure φ t)
    {γ : ℝ} {σ : ℝ → ℝ} (hγ : γ ≠ 0)
    (hσ : ∀ r, 1 ≤ r → ContDiffAt ℝ 1 σ r)
    (hgraph : ∀ r, 1 ≤ r → FeedbackGraphAt γ σ r) :
    IntegrableOn (driftCost M γ σ φ) (Ioc 0 (L : ℝ)) ∧
      IntegrableOn (fun x => M.typeDensity x ^ 2 * massCost M γ σ φ x) (Ioc 0 (L : ℝ)) ∧
      IntegrableOn (massCost M γ σ φ) (Ioc 0 (L : ℝ)) (continuousSingularMass M) ∧
      statePotential γ σ (clippedState M φ L 0) - statePotential γ σ (clippedState M φ L L) =
        1 / 2 * (∫ x in Ioc 0 (L : ℝ), driftCost M γ σ φ x) +
          1 / 2 * (∫ x in Ioc 0 (L : ℝ), M.typeDensity x ^ 2 * massCost M γ σ φ x) +
          1 / 2 * (∫ x in Ioc 0 (L : ℝ), massCost M γ σ φ x ∂continuousSingularMass M) +
          ∑' x : actualAtoms M L, actualAtomLoss M γ σ φ x := by
  let ad : ℝ → ℝ := fun x => actualChordCoefficient M γ σ φ L x (driftDensity M φ x)
  let am : ℝ → ℝ := fun x => actualChordCoefficient M γ σ φ L x (massDensity φ x)
  have hdI : IntegrableOn ad (Ioc 0 (L : ℝ)) :=
    actualChordCoefficient_action_integrable M hc hm h₀ L hγ hσ
      (fun r hr => (hgraph r hr).positive) (ae_restrict_mem measurableSet_Ioc)
      (driftDensity_integrable M hc hm h₀ 0 L)
  have hmI : IntegrableOn am (Ioc 0 (L : ℝ)) M.measure :=
    actualChordCoefficient_action_integrable M hc hm h₀ L hγ hσ
      (fun r hr => (hgraph r hr).positive) (ae_restrict_mem measurableSet_Ioc)
      (massDensity_integrable M hc 0 L)
  obtain ⟨haI, hsI, hsplit⟩ := actual_mass_integral_split M hmI
  have hdAE : ad =ᵐ[volume.restrict (Ioc 0 (L : ℝ))] fun x => -1 / 2 * driftCost M γ σ φ x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae (volume_ae_not_massAtomSet M)] with x hx hna
    exact actualChordCoefficient_drift_of_no_atom M hc hm h₀ L hγ hσ hgraph hx
      (le_antisymm (not_lt.mp hna) bot_le)
  have hmAE : am =ᵐ[volume.restrict (Ioc 0 (L : ℝ))] fun x => -1 / 2 * massCost M γ σ φ x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae (volume_ae_not_massAtomSet M)] with x hx hna
    exact actualChordCoefficient_mass_of_no_atom M hc hm h₀ L hγ hσ hgraph hx
      (le_antisymm (not_lt.mp hna) bot_le)
  have hdCost : IntegrableOn (driftCost M γ σ φ) (Ioc 0 (L : ℝ)) := by
    apply (hdI.const_mul (-2)).congr
    filter_upwards [hdAE] with x hx
    simp only [hx]
    ring
  have haCost : IntegrableOn (fun x => M.typeDensity x ^ 2 * massCost M γ σ φ x) (Ioc 0 (L : ℝ)) := by
    apply (haI.const_mul (-2)).congr
    filter_upwards [hmAE] with x hx
    simp only [hx]
    ring
  have hsBoth : Integrable am ((continuousSingularMass M).restrict (Ioc 0 (L : ℝ)) +
      (M.measure.restrict (massAtomSet M)).restrict (Ioc 0 (L : ℝ))) := by
    rw [← Measure.restrict_add, ← singularPart_eq_continuous_add_atoms]
    exact hsI
  have hscI := hsBoth.left_of_add_measure
  have hatI := hsBoth.right_of_add_measure
  have hscAE : am =ᵐ[(continuousSingularMass M).restrict (Ioc 0 (L : ℝ))]
      fun x => -1 / 2 * massCost M γ σ φ x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (continuousSingularMass_ae_not_massAtomSet M)] with x hx hna
    exact actualChordCoefficient_mass_of_no_atom M hc hm h₀ L hγ hσ hgraph hx
      (le_antisymm (not_lt.mp hna) bot_le)
  have hscCost : IntegrableOn (massCost M γ σ φ) (Ioc 0 (L : ℝ)) (continuousSingularMass M) := by
    apply (hscI.const_mul (-2)).congr
    filter_upwards [hscAE] with x hx
    simp only [hx]
    ring
  have hatSet : Ioc (0 : ℝ) L ∩ massAtomSet M = actualAtoms M L := by
    ext x
    simp only [mem_inter_iff, actualAtoms, massAtomSet, mem_ofPred_eq]
  have hatInt : (∫ x in Ioc 0 (L : ℝ), am x ∂M.measure.restrict (massAtomSet M)) =
      -(∑' x : actualAtoms M L, actualAtomLoss M γ σ φ x) := by
    have hcount : (actualAtoms M L).Countable := (massAtomSet_countable M).mono (fun _ hx => hx.2)
    have hiat : IntegrableOn am (actualAtoms M L) M.measure := by
      simpa only [Measure.restrict_restrict measurableSet_Ioc, hatSet, IntegrableOn] using hatI
    change (∫ x, am x ∂(M.measure.restrict (massAtomSet M)).restrict (Ioc 0 (L : ℝ))) = _
    rw [Measure.restrict_restrict measurableSet_Ioc, hatSet, setIntegral_countable am hcount hiat]
    have ht : ∀ x : actualAtoms M L, M.measure.real {(x : ℝ)} * am x = -actualAtomLoss M γ σ φ x :=
      fun x => actualChordCoefficient_atom_mass M hc hm h₀ L hγ hσ hgraph x.property.1
    simp only [smul_eq_mul, ht, tsum_neg]
  have hDval : (∫ x in Ioc 0 (L : ℝ), ad x) = -1 / 2 * (∫ x in Ioc 0 (L : ℝ), driftCost M γ σ φ x) := by
    rw [← integral_const_mul]
    exact integral_congr_ae hdAE
  have hAval : (∫ x in Ioc 0 (L : ℝ), M.typeDensity x ^ 2 * am x) =
      -1 / 2 * (∫ x in Ioc 0 (L : ℝ), M.typeDensity x ^ 2 * massCost M γ σ φ x) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hmAE] with x hx
    rw [hx]
    ring
  have hSval : (∫ x in Ioc 0 (L : ℝ), am x ∂continuousSingularMass M) =
      -1 / 2 * (∫ x in Ioc 0 (L : ℝ), massCost M γ σ φ x ∂continuousSingularMass M) := by
    rw [← integral_const_mul]
    exact integral_congr_ae hscAE
  have hSing := integral_add_measure hscI hatI
  rw [← Measure.restrict_add, ← singularPart_eq_continuous_add_atoms] at hSing
  rw [hSval, hatInt] at hSing
  have hchain := actual_cadlag_physical_identity M hc hm h₀ L he hγ hσ (fun r hr => (hgraph r hr).positive)
  change (∫ x in Ioc 0 (L : ℝ), ad x) + (∫ x in Ioc 0 (L : ℝ), am x ∂M.measure) = _ at hchain
  rw [hDval, hsplit, hAval, hSing] at hchain
  exact ⟨hdCost, haCost, hscCost, by linarith⟩

/-- The complete fundamental identity for every actual physical string.
It covers singular continuous mass and all countably many nonlinear atoms,
with the origin atom excluded because it already initializes the state. -/
theorem actual_fundamental_identity (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1) (L : ℝ≥0)
    (he : ∀ x ∈ Icc 0 (L : ℝ), φ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure φ t)
    {γ : ℝ} {σ : ℝ → ℝ} (hγ : 0 < γ)
    (hσ : ∀ r, 1 ≤ r → ContDiffAt ℝ 1 σ r)
    (hgraph : ∀ r, 1 ≤ r → FeedbackGraphAt γ σ r) :
    IntegrableOn (actualSquareCost M γ σ φ) (Ioc 0 (L : ℝ)) ∧
      statePotential γ σ (clippedState M φ L 0) - statePotential γ σ (clippedState M φ L L) =
        (∫ x in Ioc 0 (L : ℝ), M.rewardDensity γ φ x) +
          1 / 2 * (∫ x in Ioc 0 (L : ℝ), actualSquareCost M γ σ φ x) +
          1 / 2 * (∫ x in Ioc 0 (L : ℝ), massCost M γ σ φ x ∂continuousSingularMass M) +
          ∑' x : actualAtoms M L, actualAtomLoss M γ σ φ x := by
  obtain ⟨hd, ha, _hs, hid⟩ := actual_cadlag_cost_identity M hc hm h₀ L he hγ.ne' hσ hgraph
  have hr := M.rewardDensity_integrableOn hγ.le hc 0 L
  have hsq : EqOn (actualSquareCost M γ σ φ) (fun x => driftCost M γ σ φ x +
      M.typeDensity x ^ 2 * massCost M γ σ φ x - 2 * M.rewardDensity γ φ x) (Ioc 0 (L : ℝ)) := by
    intro x hx
    have hp := compactStateDomain_positive_ratio M φ L (clippedState_mem M hc hm h₀ L x)
    simp only [clippedState, clipTime_of_mem L (Ioc_subset_Icc_self hx)] at hp
    exact actualSquareCost_eq M hm h₀ hx.1.le (hgraph _ hp.2.2.2).positive
  have hi : IntegrableOn (actualSquareCost M γ σ φ) (Ioc 0 (L : ℝ)) :=
    (integrableOn_congr_fun hsq measurableSet_Ioc).2 ((hd.add ha).sub (hr.const_mul 2))
  have hsquare : (∫ x in Ioc 0 (L : ℝ), actualSquareCost M γ σ φ x) =
      (∫ x in Ioc 0 (L : ℝ), driftCost M γ σ φ x) +
        (∫ x in Ioc 0 (L : ℝ), M.typeDensity x ^ 2 * massCost M γ σ φ x) -
          2 * (∫ x in Ioc 0 (L : ℝ), M.rewardDensity γ φ x) := by
    rw [setIntegral_congr_fun measurableSet_Ioc hsq]
    simpa only [Pi.add_apply, integral_add hd ha, integral_const_mul] using
      integral_sub (hd.add ha) (hr.const_mul 2)
  exact ⟨hi, by linarith⟩

end
end krylov.ContinuumBV
