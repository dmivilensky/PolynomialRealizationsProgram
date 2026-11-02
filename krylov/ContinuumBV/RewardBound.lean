import krylov.ContinuumBV.FundamentalIdentity

/-!
Article: main_krylov, thm:value, upper bound for all admissible strings.
Use: obtain the genuine finite-prefix and extended infinite reward bounds
from the full BV fundamental identity, retaining singular and atomic losses.
Source: positivity of the actual potential and of every proved loss term.
-/

namespace krylov.ContinuumBV
noncomputable section
open Set Filter MeasureTheory
open krylov.Strings krylov.ContinuumControl
open scoped Topology NNReal

/-- The initial unit atom initializes all three normalized coordinates. -/
theorem statePotential_clipped_zero (M : Mass) {φ : ℝ → ℝ} (h₀ : φ 0 = 1) (L : ℝ≥0)
    (γ : ℝ) (σ : ℝ → ℝ) :
    statePotential γ σ (clippedState M φ L 0) = feedbackValue γ σ 1 := by
  simp [statePotential, stateValue, clippedState, clipTime_of_mem L ⟨le_rfl, L.property⟩,
    integralSlope, integralEnergy, h₀]

/-- The square loss is genuinely nonnegative at every physical point. -/
theorem actualSquareCost_nonneg (M : Mass) (γ : ℝ) (σ φ : ℝ → ℝ) (x : ℝ) :
    0 ≤ actualSquareCost M γ σ φ x := by
  apply mul_nonneg _ (sq_nonneg _)
  exact Real.rpow_nonneg (zero_le_one.trans (integralEnergy_one_le M.measure φ x)) _

/-- Every admissible mass-direction loss coefficient is strictly positive,
also at points of singular continuous mass. -/
theorem massCost_pos (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1) (L : ℝ≥0)
    (γ : ℝ) {σ : ℝ → ℝ} (hσpos : ∀ r, 1 ≤ r → 0 < σ r)
    {x : ℝ} (hx : x ∈ Icc 0 (L : ℝ)) : 0 < massCost M γ σ φ x := by
  have hp := compactStateDomain_positive_ratio M φ L (clippedState_mem M hc hm h₀ L x)
  simp only [clippedState, clipTime_of_mem L hx] at hp
  exact div_pos (mul_pos (mul_pos (Real.rpow_pos_of_pos hp.2.2.1 _) hp.1)
    (Real.sqrt_pos.2 (hσpos _ hp.2.2.2))) hp.2.1

/-- Every actual positive-position atom has strictly positive exact loss. -/
theorem actualAtomLoss_pos (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1) (L : ℝ≥0)
    {γ : ℝ} {σ : ℝ → ℝ} (hgraph : ∀ r, 1 ≤ r → FeedbackGraphAt γ σ r)
    (x : actualAtoms M L) : 0 < actualAtomLoss M γ σ φ x := by
  have hfin : M.measure {(x : ℝ)} ≠ ⊤ := by rw [M.measure_atom]; exact ENNReal.ofReal_ne_top
  have hreal : 0 < M.measure.real {(x : ℝ)} := ENNReal.toReal_pos x.property.2.ne' hfin
  exact actual_atom_loss_pos M hc hm h₀ x.property.1.1 hreal
    (graph_at_actual_impulse M hc hm h₀ L hgraph x.property.1)

/-- Every finite physical reward lies strictly below the initial potential:
the genuine terminal potential is positive, even for singular and atomic mass. -/
theorem actual_reward_integral_lt_initial (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1) (L : ℝ≥0)
    (he : ∀ x ∈ Icc 0 (L : ℝ), φ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure φ t)
    {γ : ℝ} {σ : ℝ → ℝ} (hγ : 0 < γ)
    (hσ : ∀ r, 1 ≤ r → ContDiffAt ℝ 1 σ r)
    (hgraph : ∀ r, 1 ≤ r → FeedbackGraphAt γ σ r) :
    (∫ x in Ioc 0 (L : ℝ), M.rewardDensity γ φ x) < feedbackValue γ σ 1 := by
  have hid := (actual_fundamental_identity M hc hm h₀ L he hγ hσ hgraph).2
  rw [statePotential_clipped_zero M h₀ L γ σ] at hid
  have hsq : 0 ≤ ∫ x in Ioc 0 (L : ℝ), actualSquareCost M γ σ φ x :=
    setIntegral_nonneg measurableSet_Ioc (fun x _ => actualSquareCost_nonneg M γ σ φ x)
  have hsc : 0 ≤ ∫ x in Ioc 0 (L : ℝ), massCost M γ σ φ x ∂continuousSingularMass M :=
    setIntegral_nonneg (μ := continuousSingularMass M) measurableSet_Ioc
    (fun x hx => (massCost_pos M hc hm h₀ L γ (fun r hr => (hgraph r hr).positive)
      (Ioc_subset_Icc_self hx)).le)
  have hat : 0 ≤ ∑' x : actualAtoms M L, actualAtomLoss M γ σ φ x :=
    tsum_nonneg (fun x : actualAtoms M L => (actualAtomLoss_pos M hc hm h₀ L hgraph x).le)
  have hdom := clippedState_mem M hc hm h₀ L (L : ℝ)
  have hp := compactStateDomain_positive_ratio M φ L hdom
  have hterminal : 0 < statePotential γ σ (clippedState M φ L L) :=
    stateValue_pos hγ hp.2.2.1 hdom.2 (hgraph _ hp.2.2.2).positive
  linarith

/-- Extended finite-prefix reward agrees with its real Bochner integral,
whose integrability was derived from the true RN type density. -/
theorem actual_rewardPrefix_eq_ofReal_integral (M : Mass) {γ : ℝ} (hγ : 0 ≤ γ)
    {φ : ℝ → ℝ} (hc : Continuous φ) (X : ℝ) :
    M.rewardPrefix γ φ X = ENNReal.ofReal (∫ x in Ioc 0 X, M.rewardDensity γ φ x) := by
  exact (ofReal_integral_eq_lintegral_ofReal (M.rewardDensity_integrableOn hγ hc 0 X)
    (Eventually.of_forall (fun x => M.rewardDensity_nonneg γ φ x))).symm

/-- The actual finite-prefix reward is bounded for arbitrary singular mass,
with countably many atoms allowed. -/
theorem actual_rewardPrefix_le (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1) (L : ℝ≥0)
    (he : ∀ x ∈ Icc 0 (L : ℝ), φ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure φ t)
    {γ : ℝ} {σ : ℝ → ℝ} (hγ : 0 < γ)
    (hσ : ∀ r, 1 ≤ r → ContDiffAt ℝ 1 σ r)
    (hgraph : ∀ r, 1 ≤ r → FeedbackGraphAt γ σ r) :
    M.rewardPrefix γ φ L ≤ ENNReal.ofReal (feedbackValue γ σ 1) := by
  rw [actual_rewardPrefix_eq_ofReal_integral M hγ.le hc]
  exact ENNReal.ofReal_le_ofReal (actual_reward_integral_lt_initial M hc hm h₀ L he hγ hσ hgraph).le

/-- Global upper bound on the actual extended reward. Infinite reward is
excluded by increasing finite prefixes, rather than silently mapped to zero
by a nonintegrable real integral. -/
theorem actual_reward_le (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1)
    (he : ∀ x ≥ 0, φ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure φ t)
    {γ : ℝ} {σ : ℝ → ℝ} (hγ : 0 < γ)
    (hσ : ∀ r, 1 ≤ r → ContDiffAt ℝ 1 σ r)
    (hgraph : ∀ r, 1 ≤ r → FeedbackGraphAt γ σ r) :
    M.reward γ φ ≤ ENNReal.ofReal (feedbackValue γ σ 1) := by
  apply M.reward_le_of_prefix_le γ φ
  intro X hX
  exact actual_rewardPrefix_le M hc hm h₀ ⟨X, hX⟩ (fun x hx => he x hx.1) hγ hσ hgraph

end
end krylov.ContinuumBV
