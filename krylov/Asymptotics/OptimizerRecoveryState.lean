import krylov.Asymptotics.RecoveryTypeState
import krylov.Asymptotics.FeedbackGraphs
import krylov.Strings.OptimizerRegularMaximum

/-!
Article: main_krylov, thm:limit, lower bound.
Use: the actually constructed stage-9 optimizer supplies the smooth type
data required by the finite recovery construction. Its compact type reward
is the exact initial Bellman value minus the actual terminal potential.
Source: the proved global LV orbits, physical quadratures, analytic initial
germ, genuine inverse type clock, and exact reward potential identity.
-/
namespace krylov.Asymptotics
noncomputable section
open Set Real Filter MeasureTheory
open krylov.Strings krylov.Strings.OptimizerQuadratures
open krylov.LotkaVolterra krylov.ContinuumControl
open scoped Topology

/-- The actual optimizer density is C¹ on the full physical half-line,
including the initial right germ. -/
theorem optimizerDensity_contDiffOn {γ : ℝ} {s U : ℝ → ℝ}
    (hs : Continuous s) (hU : Continuous U) (hp : ∀ t, 0 < s t)
    (h₁ : ∀ t ≥ 0, 1 ≤ s t)
    (hode : ∀ t > 0, HasDerivAt s (2 * s t * (s t - 1 - γ * U t)) t ∧
      HasDerivAt U (U t * (s t + 1 - U t)) t) :
    ContDiffOn ℝ 1 (extendedDensity s) (Ici 0) := by
  intro x hx
  change 0 ≤ x at hx
  rcases eq_or_lt_of_le hx with rfl | hx
  · exact (analyticWithinAt_extendedDensity_zero hs hU hp h₁ hode).contDiffWithinAt
  · exact (analyticAt_extendedDensity hs hp h₁ hode hx).contDiffAt.contDiffWithinAt

/-- Actual compact type-state data obtained from the genuine optimizer
quadratures. This definition constructs every coordinate and every proof. -/
def optimizerRecoveryState {γ : ℝ} {s U : ℝ → ℝ} {X : ℝ} (hX : 0 < X)
    (hs : Continuous s) (hU : Continuous U) (hp : ∀ t, 0 < s t)
    (h₁ : ∀ t ≥ 0, 1 ≤ s t) (hU₀ : U 0 = 1)
    (hode : ∀ t > 0, HasDerivAt s (2 * s t * (s t - 1 - γ * U t)) t ∧
      HasDerivAt U (U t * (s t + 1 - U t)) t) :
    RecoveryState (recoveryTypeClock (extendedDensity s) X) :=
  physicalRecoveryState hX (extendedDensity_continuous hs hp h₁)
    (extendedDensity_pos hp) (optimizerDensity_contDiffOn hs hU hp h₁ hode)
    (extended_coordinates_continuous hs hU hp h₁).1
    (extended_coordinates_continuous hs hU hp h₁).2.1
    (extended_coordinates_continuous hs hU hp h₁).2.2
    (extended_initial (U := U) hs hp).1
    (extended_initial (U := U) hs hp).2.1
    (extended_initial (U := U) hs hp).2.2
    (fun _ hx ↦ extended_smoothStringAt hs hU hp h₁ hU₀ (fun t ht ↦ (hode t ht).2) hx)

theorem optimizerRecoveryState_energy {γ : ℝ} {s U : ℝ → ℝ} {X : ℝ} (hX : 0 < X)
    (hs : Continuous s) (hU : Continuous U) (hp : ∀ t, 0 < s t)
    (h₁ : ∀ t ≥ 0, 1 ≤ s t) (hU₀ : U 0 = 1)
    (hode : ∀ t > 0, HasDerivAt s (2 * s t * (s t - 1 - γ * U t)) t ∧
      HasDerivAt U (U t * (s t + 1 - U t)) t) :
    (optimizerRecoveryState hX hs hU hp h₁ hU₀ hode).energy =
      recoveryTypePullback (extendedDensity s) X (extendedEnergy s U) := rfl

/-- Exact reward of the constructed optimizer type state. Both the inverse
clock substitution and the original physical Bellman identity are proved. -/
theorem optimizerRecoveryState_reward {γ : ℝ} {s U : ℝ → ℝ} {X : ℝ}
    (hγ : γ ≠ 0) (hX : 0 < X) (hs : Continuous s) (hU : Continuous U)
    (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t) (hU₀ : U 0 = 1)
    (hUp : ∀ t ≥ 0, 0 < U t)
    (hode : ∀ t > 0, HasDerivAt s (2 * s t * (s t - 1 - γ * U t)) t ∧
      HasDerivAt U (U t * (s t + 1 - U t)) t) :
    let R := optimizerRecoveryState hX hs hU hp h₁ hU₀ hode
    (∫ y in 0..recoveryTypeClock (extendedDensity s) X, R.energy y ^ (-γ)) =
      sqrt (s 0) / (2 * γ) - physicalOrbitValue γ s U X := by
  obtain ⟨hcφ, hcp, hcK⟩ := extended_coordinates_continuous hs hU hp h₁
  obtain ⟨hφ₀, hp₀, hK₀⟩ := extended_initial (U := U) hs hp
  have ht := physicalRecoveryState_reward (γ := γ) hX (extendedDensity_continuous hs hp h₁)
    (extendedDensity_pos hp) (optimizerDensity_contDiffOn hs hU hp h₁ hode)
    hcφ hcp hcK hφ₀ hp₀ hK₀
    (fun _ hx ↦ extended_smoothStringAt hs hU hp h₁ hU₀ (fun t ht ↦ (hode t ht).2) hx)
  change (∫ y in 0..recoveryTypeClock (extendedDensity s) X,
    (optimizerRecoveryState hX hs hU hp h₁ hU₀ hode).energy y ^ (-γ)) = _
  have heq : (∫ y in 0..recoveryTypeClock (extendedDensity s) X,
      (optimizerRecoveryState hX hs hU hp h₁ hU₀ hode).energy y ^ (-γ)) =
      ∫ x in 0..X, extendedEnergy s U x ^ (-γ) * extendedDensity s x := by
    rw [optimizerRecoveryState_energy]
    exact ht
  rw [heq]
  exact (orbitRewardRate_integral hγ hs hU hp h₁ hUp hode hX.le).trans
    (by rw [physicalOrbitValue_initial hs hp hU₀])

/-- Vanishing actual terminal potential produces genuine smooth compact
type states with reward arbitrarily close to the sharp continuum value. -/
theorem exists_optimizerRecoveryState_near_value {γ : ℝ} {s U : ℝ → ℝ}
    (hγ : γ ≠ 0) (hs : Continuous s) (hU : Continuous U)
    (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t) (hU₀ : U 0 = 1)
    (hUp : ∀ t ≥ 0, 0 < U t)
    (hode : ∀ t > 0, HasDerivAt s (2 * s t * (s t - 1 - γ * U t)) t ∧
      HasDerivAt U (U t * (s t + 1 - U t)) t)
    (hterm : Tendsto (physicalOrbitValue γ s U) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Y > (0 : ℝ), ∃ R : RecoveryState Y,
      sqrt (s 0) / (2 * γ) - ε < ∫ y in 0..Y, R.energy y ^ (-γ) := by
  have he := hterm.eventually (Iio_mem_nhds hε)
  obtain ⟨X, hX, hv⟩ := ((eventually_gt_atTop (0 : ℝ)).and he).exists
  refine ⟨recoveryTypeClock (extendedDensity s) X,
    recoveryTypeClock_pos (extendedDensity_continuous hs hp h₁) (extendedDensity_pos hp) hX,
    optimizerRecoveryState hX hs hU hp h₁ hU₀ hode, ?_⟩
  rw [optimizerRecoveryState_reward hγ hX hs hU hp h₁ hU₀ hUp hode]
  linarith

end
end krylov.Asymptotics
