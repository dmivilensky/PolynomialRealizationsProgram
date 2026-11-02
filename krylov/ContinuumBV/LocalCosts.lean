import krylov.ContinuumBV.Optimality
import krylov.Strings.LocalCompatibility
import krylov.ContinuumBV.FiniteRewardBound

/-!
Article: main_krylov, thm:value, locality of the equality losses.
Use: compare compact representatives of a finite-endpoint string without
assuming that its mass or state extend through the excluded endpoint.
Source: restriction of Stieltjes measures, RN locality and the actual jump law.
-/

namespace krylov.ContinuumBV
noncomputable section
open Set Filter MeasureTheory
open krylov.Strings krylov.ContinuumControl
open scoped Topology NNReal

/-- Equality of physical mass restrictions preserves every interior singleton. -/
theorem singleton_eq_of_restrict_eq (M N : Mass) {L x : ℝ}
    (hμ : M.measure.restrict (Ioc 0 L) = N.measure.restrict (Ioc 0 L))
    (hx : x ∈ Ioc 0 L) : M.measure {x} = N.measure {x} := by
  have h := congrArg (fun μ : Measure ℝ ↦ μ {x}) hμ
  simpa only [Measure.restrict_apply (measurableSet_singleton x),
    inter_eq_left.mpr (singleton_subset_iff.mpr hx)] using h

/-- The actual mass coordinates are local in both the mass and the position. -/
theorem coordinates_eq_of_restrict_eq (M N : Mass) {φ ψ : ℝ → ℝ} {L x : ℝ}
    (hμ : M.measure.restrict (Ioc 0 L) = N.measure.restrict (Ioc 0 L))
    (hφ : EqOn φ ψ (Icc 0 L)) (hx : x ∈ Icc 0 L) :
    integralSlope M.measure φ x = integralSlope N.measure ψ x ∧
      integralEnergy M.measure φ x = integralEnergy N.measure ψ x := by
  have hr := M.restrict_initial_eq_of_restrict_eq N hμ hx.2
  constructor
  · calc
      integralSlope M.measure φ x = integralSlope M.measure ψ x :=
        M.slope_eq_of_eqOn (fun _ ht ↦ hφ ⟨ht.1, ht.2.trans hx.2⟩)
      _ = integralSlope N.measure ψ x := by simp only [integralSlope, hr]
  · calc
      integralEnergy M.measure φ x = integralEnergy M.measure ψ x :=
        M.energy_eq_of_eqOn (fun _ ht ↦ hφ ⟨ht.1, ht.2.trans hx.2⟩)
      _ = integralEnergy N.measure ψ x := by simp only [integralEnergy, hr]

/-- The ordinary mass-direction coefficient depends only on physical history. -/
theorem massCost_eq_of_restrict_eq (M N : Mass) {φ ψ : ℝ → ℝ} {L x : ℝ}
    (hμ : M.measure.restrict (Ioc 0 L) = N.measure.restrict (Ioc 0 L))
    (hφ : EqOn φ ψ (Icc 0 L)) (hx : x ∈ Icc 0 L) (γ : ℝ) (σ : ℝ → ℝ) :
    massCost M γ σ φ x = massCost N γ σ ψ x := by
  obtain ⟨hp, hK⟩ := coordinates_eq_of_restrict_eq M N hμ hφ hx
  simp only [massCost, hφ hx, hp, hK]

/-- The actual square losses agree almost everywhere on the common window.
Only RN densities require an almost-everywhere statement. -/
theorem actualSquareCost_eq_ae_of_restrict_eq (M N : Mass) {φ ψ : ℝ → ℝ} {L : ℝ}
    (hμ : M.measure.restrict (Ioc 0 L) = N.measure.restrict (Ioc 0 L))
    (hφ : EqOn φ ψ (Icc 0 L)) (γ : ℝ) (σ : ℝ → ℝ) :
    actualSquareCost M γ σ φ =ᵐ[volume.restrict (Ioc 0 L)] actualSquareCost N γ σ ψ := by
  filter_upwards [M.typeDensity_eq_ae_of_restrict_eq N hμ,
    ae_restrict_mem measurableSet_Ioc] with x hv hx
  obtain ⟨hp, hK⟩ := coordinates_eq_of_restrict_eq M N hμ hφ (Ioc_subset_Icc_self hx)
  simp only [actualSquareCost, hφ (Ioc_subset_Icc_self hx), hp, hK, hv]

/-- Compact reward is local in the actual measure and physical history. -/
theorem rewardPrefix_eq_of_restrict_eq (M N : Mass) {φ ψ : ℝ → ℝ} {L : ℝ}
    (hμ : M.measure.restrict (Ioc 0 L) = N.measure.restrict (Ioc 0 L))
    (hφ : EqOn φ ψ (Icc 0 L)) (γ : ℝ) : M.rewardPrefix γ φ L = N.rewardPrefix γ ψ L := by
  apply lintegral_congr_ae
  filter_upwards [M.typeDensity_eq_ae_of_restrict_eq N hμ,
    ae_restrict_mem measurableSet_Ioc] with x hv hx
  have hK := (coordinates_eq_of_restrict_eq M N hμ hφ (Ioc_subset_Icc_self hx)).2
  simp only [Mass.rewardDensity, hK, hv]

/-- Even the nonlinear impulse loss is local: its true pre-state is recovered
from the proved exact atom update, not supplied as extra impulse data. -/
theorem actualAtomLoss_eq_of_restrict_eq (M N : Mass) {φ ψ : ℝ → ℝ} {L x : ℝ}
    (hcφ : Continuous φ) (hcψ : Continuous ψ)
    (hμ : M.measure.restrict (Ioc 0 L) = N.measure.restrict (Ioc 0 L))
    (hφ : EqOn φ ψ (Icc 0 L)) (hx : x ∈ Ioc 0 L) (γ : ℝ) (σ : ℝ → ℝ) :
    actualAtomLoss M γ σ φ x = actualAtomLoss N γ σ ψ x := by
  have hm := singleton_eq_of_restrict_eq M N hμ hx
  have hr : M.measure.real {x} = N.measure.real {x} := congrArg ENNReal.toReal hm
  have hφx := hφ (Ioc_subset_Icc_self hx)
  obtain ⟨hp, hK⟩ := coordinates_eq_of_restrict_eq M N hμ hφ (Ioc_subset_Icc_self hx)
  have hpL : Function.leftLim (integralSlope M.measure φ) x =
      Function.leftLim (integralSlope N.measure ψ) x := by
    have hM := M.slope_atom_update hcφ hx.1
    have hN := N.slope_atom_update hcψ hx.1
    rw [hp, hr, hφx] at hM
    linarith
  have hKL : Function.leftLim (integralEnergy M.measure φ) x =
      Function.leftLim (integralEnergy N.measure ψ) x := by
    have hM := M.energy_atom_update hcφ hx.1
    have hN := N.energy_atom_update hcψ hx.1
    rw [hK, hr, hφx] at hM
    linarith
  simp only [actualAtomLoss, hφx, hpL, hKL, hr]

/-- The singular part of mass is local on every physical compact window. -/
theorem singularPart_eq_of_restrict_eq (M N : Mass) {L : ℝ}
    (hμ : M.measure.restrict (Ioc 0 L) = N.measure.restrict (Ioc 0 L)) :
    (M.measure.singularPart volume).restrict (Ioc 0 L) =
      (N.measure.singularPart volume).restrict (Ioc 0 L) := by
  have : IsLocallyFiniteMeasure M.measure := by dsimp [Mass.measure]; infer_instance
  have : IsLocallyFiniteMeasure N.measure := by dsimp [Mass.measure]; infer_instance
  rw [← Measure.singularPart_restrict _ _ measurableSet_Ioc,
    ← Measure.singularPart_restrict _ _ measurableSet_Ioc, hμ]

/-- Removing actual atoms commutes with localization of singular mass. -/
theorem continuousSingularMass_eq_of_restrict_eq (M N : Mass) {L : ℝ}
    (hμ : M.measure.restrict (Ioc 0 L) = N.measure.restrict (Ioc 0 L)) :
    (continuousSingularMass M).restrict (Ioc 0 L) =
      (continuousSingularMass N).restrict (Ioc 0 L) := by
  unfold continuousSingularMass
  rw [Measure.restrict_comm measurableSet_Ioc, singularPart_eq_of_restrict_eq M N hμ,
    Measure.restrict_comm measurableSet_Ioc]
  apply Measure.restrict_congr_set
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  apply propext
  change (¬0 < M.measure {x}) ↔ (¬0 < N.measure {x})
  rw [singleton_eq_of_restrict_eq M N hμ hx]

end
end krylov.ContinuumBV
