import krylov.Asymptotics.StepLoss
import krylov.Asymptotics.WeightedLogSums

/-!
Article: main_krylov, upper bound in thm:limit.
Use: the actual finite drift/impulse loss budget telescopes below the true
continuum initial value. This retains arbitrary terminal Robin parameters;
the physical state itself is fixed by the genuine discrete string.
Source: the proved one-step integral identity and positive terminal potential.
-/
namespace krylov.Asymptotics
noncomputable section
open Real Finset
open krylov.Strings krylov.ContinuumControl
open scoped BigOperators

namespace DiscreteString
variable {N : ℕ} (S : krylov.Strings.DiscreteString N)

/-- Actual decrease of the continuum value along one finite-string edge. -/
def potentialLoss (γ : ℝ) (σ : ℝ → ℝ) (j : ℕ) : ℝ :=
  stateValue γ σ (S.φ j) (S.p j) (S.K j) -
    stateValue γ σ (S.φ (j + 1)) (S.p (j + 1)) (S.K (j + 1))

/-- The post-mass energy weight is below the pre-drift weight. -/
theorem energyWeight_le_before {γ : ℝ} (hγ : 0 ≤ γ) {j : ℕ} (hj : j < N) :
    energyWeight S γ j ≤ S.K j ^ (-γ) := by
  have hK := (S.state_bounds j hj.le).2.2.1
  exact Real.rpow_le_rpow_of_nonpos (by linarith) (coordinates_strict S hj).2.2.le
    (neg_nonpos.mpr hγ)

/-- The actual sum of edge losses is at most the continuum initial value. -/
theorem potentialLoss_sum_le {γ : ℝ} {σ : ℝ → ℝ} (hγ : 0 < γ)
    (hgraph : ∀ r ≥ 1, FeedbackGraphAt γ σ r) :
    (∑ j ∈ range N, potentialLoss S γ σ j) ≤ feedbackValue γ σ 1 := by
  simp only [potentialLoss]
  rw [sum_range_sub']
  obtain ⟨_, _, hK, hdom⟩ := S.state_bounds N le_rfl
  have hterminal := stateValue_pos hγ (show 0 < S.K N by linarith) hdom
    (hgraph _ (S.ratio_ge_one N le_rfl)).positive
  have hinit : stateValue γ σ (S.φ 0) (S.p 0) (S.K 0) = feedbackValue γ σ 1 := by
    simp [stateValue]
  rw [hinit]
  linarith

/-- Actual integrated step costs fit in twice the true continuum value. -/
theorem integrated_cost_budget {γ : ℝ} {σ : ℝ → ℝ} (hγ : 0 < γ)
    (hgraph : ∀ r ≥ 1, FeedbackGraphAt γ σ r) :
    (∑ j ∈ range N, (S.K j ^ (-γ) * driftIntegral S σ j +
      energyWeight S γ j * impulseIntegral S σ j)) ≤ 2 * feedbackValue γ σ 1 := by
  have hsum : (∑ j ∈ range N, (S.K j ^ (-γ) * driftIntegral S σ j +
      energyWeight S γ j * impulseIntegral S σ j)) ≤
      2 * ∑ j ∈ range N, potentialLoss S γ σ j := by
    rw [mul_sum]
    apply sum_le_sum
    intro j hj
    have h := step_potential_ge S hgraph hγ (mem_range.mp hj)
    change 1 / 2 * (S.K j ^ (-γ) * driftIntegral S σ j +
      energyWeight S γ j * impulseIntegral S σ j) ≤ potentialLoss S γ σ j at h
    linarith only [h]
  linarith only [hsum, potentialLoss_sum_le S hγ hgraph]

end DiscreteString
end
end krylov.Asymptotics
