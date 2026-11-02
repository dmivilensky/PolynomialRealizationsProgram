import krylov.Strings.OptimizerUniqueMaximum
import krylov.Strings.OptimizerWindowUniqueness
import krylov.ContinuumBV.FiniteEquality

/-!
Article: main_krylov, thm:value, strict nonattainment at finite length.
Use: hypothetical finite-length equality forces every compact state and mass
to equal the global optimizer. Its reward is then bounded by the global
optimizer's prefix at the finite endpoint, which leaves a positive terminal
potential. Endpoint mass divergence is allowed throughout.
Source: local BV equality consequences, actual right-ODE uniqueness and the
proved strictly positive finite terminal potential.
-/

namespace krylov.Strings.OptimizerFinite
noncomputable section
open Set Filter MeasureTheory
open krylov.ContinuumBV krylov.ContinuumControl
open scoped Topology NNReal ENNReal

/-- A hypothetical finite-length optimizer has the actual global optimizer's reward prefixes. -/
theorem optimal_prefix_eq_global (N : Mass) {ψ σ : ℝ → ℝ} {γ ℓ : ℝ}
    (hcψ : Continuous ψ) (hmψ : Monotone ψ) (hψ₀ : ψ 0 = 1)
    (heψ : ∀ x ≥ 0, ψ x = 1 + ∫ t in Ioc 0 x, integralSlope N.measure ψ t)
    (hγ : 0 < γ) (hσ : ∀ r ≥ 1, ContDiffAt ℝ 1 σ r)
    (hgraph : ∀ r ≥ 1, FeedbackGraphAt γ σ r)
    (hoptN : N.reward γ ψ = ENNReal.ofReal (feedbackValue γ σ 1))
    (hℓ : 0 < ℓ) (f : StieltjesFunction (Ico (0 : ℝ) ℓ))
    (h₀ : f ⟨0, ⟨le_rfl, hℓ⟩⟩ = 1) {φ : ℝ → ℝ}
    (hc : ContinuousOn φ (Iio ℓ)) (hm : MonotoneOn φ (Iio ℓ)) (hz : φ 0 = 1)
    (he : ∀ w : Windows ℓ, ∀ x ∈ Icc 0 (w.val : ℝ), φ x = 1 +
      ∫ t in Ioc 0 x, integralSlope (windowMass hℓ f h₀ w).measure φ t)
    (hopt : reward hℓ f h₀ γ φ = ENNReal.ofReal (feedbackValue γ σ 1))
    (w : Windows ℓ) :
    (windowMass hℓ f h₀ w).rewardPrefix γ φ w.val = N.rewardPrefix γ ψ w.val := by
  let M := windowMass hℓ f h₀ w
  obtain ⟨χ, hcχ, hmχ, hχ₀, hφχ, heχ⟩ := exists_compact_state_extension hℓ f h₀ hc hm hz w (he w)
  obtain ⟨haM, hSM, hvM⟩ := optimal_window_conditions hℓ f h₀ hc hm hz he hγ hσ hgraph hopt
    w hcχ hmχ hχ₀ hφχ
  have haN := (actual_optimal_losses_zero N hcψ hmψ hψ₀ heψ hγ hσ hgraph hoptN).2.2
  have hSN := actual_optimal_singularPart_zero N hcψ hmψ hψ₀ heψ hγ hσ hgraph hoptN w.val
  have hvN : N.typeDensity =ᵐ[volume.restrict (Ioc 0 (w.val : ℝ))] actualFeedbackDensity N ψ σ :=
    actual_optimal_feedback N hcψ hmψ hψ₀ heψ hγ hσ hgraph hoptN w.val
  have hvM' : M.typeDensity =ᵐ[volume.restrict (Ioc 0 (w.val : ℝ))] actualFeedbackDensity M χ σ := hvM
  have hMcont := M.actualFeedbackState_continuousOn_window w.val hcχ haM
  have hNcont : ContinuousOn (actualFeedbackState N ψ) (Icc 0 (w.val : ℝ)) :=
    (hcψ.prodMk ((N.slope_continuous_of_no_atoms hcψ haN).prodMk
      (N.energy_continuous_of_no_atoms hcψ haN))).continuousOn
  have hstate : EqOn (actualFeedbackState M χ) (actualFeedbackState N ψ) (Icc 0 (w.val : ℝ)) := by
    apply feedback_state_unique_window w.val hσ (fun r hr ↦ (hgraph r hr).positive) hMcont hNcont
      (fun x hx ↦ actualFeedbackState_hasDerivWithinAt_window M w.val hcχ hmχ hχ₀ heχ haM
        (fun r hr ↦ (hσ r hr).continuousAt) (fun r hr ↦ (hgraph r hr).positive) hSM hvM' hx)
      (fun x hx ↦ optimal_actualState_hasDerivWithinAt N hcψ hmψ hψ₀ heψ hγ hσ hgraph hoptN hx.1)
      (fun x hx ↦ actualFeedbackState_domain M hcχ hmχ hχ₀ hx.1)
      (fun x hx ↦ actualFeedbackState_domain N hcψ hmψ hψ₀ hx.1)
    simp [actualFeedbackState, integralSlope, integralEnergy, hχ₀, hψ₀]
  have hμ := restrict_eq_of_feedback_state_eq M N w.val hSM hSN hvM' hvN hstate
  have hχψ : EqOn χ ψ (Icc 0 (w.val : ℝ)) := by
    intro x hx
    exact congrArg Prod.fst (hstate hx)
  exact rewardPrefix_eq_of_restrict_eq M N hμ (fun x hx ↦ (hφχ hx).trans (hχψ hx)) γ

/-- Every actual finite-length string has strictly smaller reward than an
attained global continuum value. No bounded endpoint mass is assumed. -/
theorem reward_lt_of_global_optimizer (N : Mass) {ψ σ : ℝ → ℝ} {γ ℓ : ℝ}
    (hN : IsState N ψ) (hγ : 0 < γ) (hσ : ∀ r ≥ 1, ContDiffAt ℝ 1 σ r)
    (hgraph : ∀ r ≥ 1, FeedbackGraphAt γ σ r)
    (hoptN : N.reward γ ψ = ENNReal.ofReal (feedbackValue γ σ 1))
    (hℓ : 0 < ℓ) (f : StieltjesFunction (Ico (0 : ℝ) ℓ))
    (h₀ : f ⟨0, ⟨le_rfl, hℓ⟩⟩ = 1) {φ : ℝ → ℝ}
    (hc : ContinuousOn φ (Iio ℓ)) (hm : MonotoneOn φ (Iio ℓ)) (hz : φ 0 = 1)
    (he : ∀ w : Windows ℓ, ∀ x ∈ Icc 0 (w.val : ℝ), φ x = 1 +
      ∫ t in Ioc 0 x, integralSlope (windowMass hℓ f h₀ w).measure φ t) :
    reward hℓ f h₀ γ φ < ENNReal.ofReal (feedbackValue γ σ 1) := by
  have hle := reward_le hℓ f h₀ hc hm hz he hγ hσ hgraph
  by_contra hnot
  have hopt : reward hℓ f h₀ γ φ = ENNReal.ofReal (feedbackValue γ σ 1) :=
    le_antisymm hle (not_lt.mp hnot)
  obtain ⟨ψ', hcψ, hψ₀, hmψ, _, heψ⟩ := N.exists_global_state
  have hEq := N.global_state_unique hN.1 hcψ hN.2.2 heψ
  have hoptN' : N.reward γ ψ' = ENNReal.ofReal (feedbackValue γ σ 1) :=
    (N.reward_eq_of_eqOn γ hEq).symm.trans hoptN
  have hprefix : reward hℓ f h₀ γ φ ≤ N.rewardPrefix γ ψ' ℓ := by
    apply iSup_le
    intro w
    rw [optimal_prefix_eq_global N hcψ hmψ hψ₀ heψ hγ hσ hgraph hoptN'
      hℓ f h₀ hc hm hz he hopt w]
    exact N.rewardPrefix_mono γ ψ' w.property.le
  have hstrict : N.rewardPrefix γ ψ' ℓ < ENNReal.ofReal (feedbackValue γ σ 1) := by
    rw [actual_rewardPrefix_eq_ofReal_integral N hγ.le hcψ]
    exact (ENNReal.ofReal_lt_ofReal_iff (feedbackValue_pos hγ le_rfl (hgraph 1 le_rfl).positive)).2
      (actual_reward_integral_lt_initial N hcψ hmψ hψ₀ ⟨ℓ, hℓ.le⟩ (fun x hx ↦ heψ x hx.1) hγ hσ hgraph)
  exact (not_lt_of_ge (hopt.symm ▸ hprefix)) hstrict

/-- The finite reward depends only on the source state on its physical
domain, so its negative extension is immaterial. -/
theorem reward_eq_of_eqOn {ℓ : ℝ} (hℓ : 0 < ℓ)
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ)) (h₀ : f ⟨0, ⟨le_rfl, hℓ⟩⟩ = 1)
    (γ : ℝ) {φ ψ : ℝ → ℝ} (h : EqOn φ ψ (Ico 0 ℓ)) :
    reward hℓ f h₀ γ φ = reward hℓ f h₀ γ ψ := by
  unfold reward
  congr 1
  funext w
  exact Mass.rewardPrefix_eq_of_eqOn _ γ (fun _ ht ↦ h ⟨ht.1, ht.2.trans_lt w.property⟩)

/-- Strict finite-length nonattainment from the original continuous state
equation alone. Monotonicity and positivity are derived, including when
the cumulative mass diverges at the excluded endpoint. -/
theorem reward_lt_of_state (N : Mass) {ψ σ : ℝ → ℝ} {γ ℓ : ℝ}
    (hN : IsState N ψ) (hγ : 0 < γ) (hσ : ∀ r ≥ 1, ContDiffAt ℝ 1 σ r)
    (hgraph : ∀ r ≥ 1, FeedbackGraphAt γ σ r)
    (hoptN : N.reward γ ψ = ENNReal.ofReal (feedbackValue γ σ 1))
    (hℓ : 0 < ℓ) (f : StieltjesFunction (Ico (0 : ℝ) ℓ))
    (h₀ : f ⟨0, ⟨le_rfl, hℓ⟩⟩ = 1) {φ : ℝ → ℝ}
    (hc : ContinuousOn φ (Iio ℓ))
    (he : ∀ w : Windows ℓ, ∀ x ∈ Icc 0 (w.val : ℝ), φ x = 1 +
      ∫ t in Ioc 0 x, integralSlope (windowMass hℓ f h₀ w).measure φ t) :
    reward hℓ f h₀ γ φ < ENNReal.ofReal (feedbackValue γ σ 1) := by
  obtain ⟨χ, hcχ, hχ₀, hmχ, _, heχ⟩ := exists_state hℓ f h₀
  have hEq := state_unique hℓ f h₀ hc hcχ he heχ
  rw [reward_eq_of_eqOn hℓ f h₀ γ hEq]
  exact reward_lt_of_global_optimizer N hN hγ hσ hgraph hoptN hℓ f h₀ hcχ hmχ hχ₀ heχ

end
end krylov.Strings.OptimizerFinite
