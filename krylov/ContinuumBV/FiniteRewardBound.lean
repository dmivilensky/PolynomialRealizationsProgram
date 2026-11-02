import krylov.ContinuumBV.RewardBound
import krylov.Strings.OptimizerFiniteCoordinates

/-!
Article: main_krylov, s3:def:string and thm:value, finite physical lengths.
Use: apply the full arbitrary-mass BV inequality to every compact subwindow
of [0,ℓ), with no boundedness or continuous extension at the excluded endpoint.
The reward is the increasing supremum of genuine RN-defined compact rewards.
Source: compact Stieltjes representatives, exact locality and monotone exhaustion.
-/

namespace krylov.Strings
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace Mass

/-- Equal position histories have equal actual string energies. -/
theorem energy_eq_of_eqOn (M : Mass) {φ ψ : ℝ → ℝ} {x : ℝ}
    (h : EqOn φ ψ (Icc 0 x)) : integralEnergy M.measure φ x = integralEnergy M.measure ψ x := by
  dsimp [integralEnergy]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  change φ t ^ 2 = ψ t ^ 2
  rw [h ⟨ht.1.le, ht.2⟩]

/-- The genuine RN reward on a compact window depends only on the position
history in that window; its values or continuity beyond the window are irrelevant. -/
theorem rewardPrefix_eq_of_eqOn (M : Mass) (γ : ℝ) {φ ψ : ℝ → ℝ} {L : ℝ}
    (h : EqOn φ ψ (Icc 0 L)) : M.rewardPrefix γ φ L = M.rewardPrefix γ ψ L := by
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro x hx
  dsimp [rewardDensity]
  rw [M.energy_eq_of_eqOn (fun t ht ↦ h ⟨ht.1, ht.2.trans hx.2⟩)]

end Mass

namespace OptimizerFinite
open krylov.ContinuumBV krylov.ContinuumControl
open scoped NNReal

/-- The full finite-endpoint reward, obtained from its genuine compact mass
representatives. The endpoint is excluded even when mass diverges there. -/
def reward {ℓ : ℝ} (hℓ : 0 < ℓ) (f : StieltjesFunction (Ico (0 : ℝ) ℓ))
    (h₀ : f ⟨0, ⟨le_rfl, hℓ⟩⟩ = 1) (γ : ℝ) (φ : ℝ → ℝ) : ℝ≥0∞ :=
  ⨆ w : Windows ℓ, (windowMass hℓ f h₀ w).rewardPrefix γ φ w.val

/-- Exact source upper bound on each actual finite-endpoint prefix. Its proof
extends only that compact position history, preserving its state equation. -/
theorem rewardPrefix_le {ℓ : ℝ} (hℓ : 0 < ℓ)
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ)) (h₀ : f ⟨0, ⟨le_rfl, hℓ⟩⟩ = 1)
    {φ : ℝ → ℝ} (hc : ContinuousOn φ (Iio ℓ)) (hm : MonotoneOn φ (Iio ℓ))
    (hz : φ 0 = 1) (w : Windows ℓ)
    (he : ∀ x ∈ Icc 0 (w.val : ℝ), φ x = 1 +
      ∫ t in Ioc 0 x, integralSlope (windowMass hℓ f h₀ w).measure φ t)
    {γ : ℝ} {σ : ℝ → ℝ} (hγ : 0 < γ)
    (hσ : ∀ r, 1 ≤ r → ContDiffAt ℝ 1 σ r)
    (hgraph : ∀ r, 1 ≤ r → FeedbackGraphAt γ σ r) :
    (windowMass hℓ f h₀ w).rewardPrefix γ φ w.val ≤
      ENNReal.ofReal (feedbackValue γ σ 1) := by
  let φw : ℝ → ℝ := IccExtend w.val.property (stateRestriction hc w)
  have hagree : EqOn φ φw (Icc 0 (w.val : ℝ)) := by
    intro t ht
    exact (IccExtend_of_mem w.val.property (stateRestriction hc w) ht).symm
  rw [Mass.rewardPrefix_eq_of_eqOn _ γ hagree]
  apply actual_rewardPrefix_le _ (stateRestriction hc w).continuous.Icc_extend'
    ((stateRestriction_monotone hc hm w).IccExtend w.val.property)
    ((hagree ⟨le_rfl, w.val.property⟩).symm.trans hz) w.val
    (Mass.position_equation_congr _ w.val he hagree) hγ hσ hgraph

/-- The actual full finite-length reward obeys the same value bound as the
half-line problem, including endpoint mass blowup, singular continuous mass
and countably many atoms. No terminal-limit hypothesis is imposed. -/
theorem reward_le {ℓ : ℝ} (hℓ : 0 < ℓ)
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ)) (h₀ : f ⟨0, ⟨le_rfl, hℓ⟩⟩ = 1)
    {φ : ℝ → ℝ} (hc : ContinuousOn φ (Iio ℓ)) (hm : MonotoneOn φ (Iio ℓ))
    (hz : φ 0 = 1)
    (he : ∀ w : Windows ℓ, ∀ x ∈ Icc 0 (w.val : ℝ), φ x = 1 +
      ∫ t in Ioc 0 x, integralSlope (windowMass hℓ f h₀ w).measure φ t)
    {γ : ℝ} {σ : ℝ → ℝ} (hγ : 0 < γ)
    (hσ : ∀ r, 1 ≤ r → ContDiffAt ℝ 1 σ r)
    (hgraph : ∀ r, 1 ≤ r → FeedbackGraphAt γ σ r) :
    reward hℓ f h₀ γ φ ≤ ENNReal.ofReal (feedbackValue γ σ 1) := by
  apply iSup_le
  intro w
  exact rewardPrefix_le hℓ f h₀ hc hm hz w (he w) hγ hσ hgraph

end OptimizerFinite
end
end krylov.Strings
