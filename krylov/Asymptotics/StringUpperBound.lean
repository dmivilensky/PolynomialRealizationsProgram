import krylov.Asymptotics.AveragingBounds
import krylov.Asymptotics.PotentialBudget
import krylov.Asymptotics.BondSiteAlgebra
import krylov.Asymptotics.FiniteBoundAlgebra
import krylov.Strings.DiscreteTopTerminal

/-!
Article: main_krylov, upper bound in thm:limit.
Use: the sharp four-term bound for the actual finite-string response.
The top-impedance identities are the spectral-coordinate inputs; every
state, integral, average, weight and potential estimate is computed and
proved for the actual string. No response or potential bound is assumed.
Source: the proved exact drift/impulse identities and bond/site cancellation.
-/
namespace krylov.Asymptotics
noncomputable section
open Real Finset Filter
open scoped Topology
open krylov.Strings krylov.ContinuumControl
open scoped BigOperators Matrix.Norms.L2Operator

namespace DiscreteString
variable {N : ℕ} (S : krylov.Strings.DiscreteString N)

/-- Sharp finite response bound from the top coordinates of a genuine finite
string. The terminal mass condition retains its exact favorable inequality. -/
theorem sharp_upper_of_impedances {γ B Λ : ℝ} {σ : ℝ → ℝ}
    (hγ : 0 < γ) (hB₀ : 0 ≤ B) (hΛ : 0 < Λ)
    (hgraph : ∀ r ≥ 1, FeedbackGraphAt γ σ r)
    (hB : ∀ r ≥ 1, 0 ≤ logSlope σ r ∧ logSlope σ r ≤ B)
    (hprod : ∀ j < N, 1 ≤ Λ * S.mass (j + 1) * S.gap j)
    (c d : ℕ → ℝ) (hc : ∀ j < N, 0 < c j) (hd : ∀ j < N, 0 < d j)
    (hgap : ∀ j < N, sqrt Λ * S.gap j = 1 / c j + 1 / d j)
    (hmass : ∀ j < N,
      d j + (if j + 1 < N then c (j + 1) else 0) ≤ sqrt Λ * S.mass (j + 1)) :
    (∑ j ∈ range N, S.K (j + 1) ^ (-γ)) ≤
      sqrt Λ * feedbackValue γ σ 1 / 2 + (1 + B) / 4 * log (1 + Λ) +
        1 / 2 + (1 + 2 * B) / (4 * γ) := by
  cases N with
  | zero =>
    simp only [sum_range_zero]
    have hf := feedbackValue_pos hγ (le_refl (1 : ℝ)) (hgraph 1 le_rfl).positive
    have hl : 0 ≤ log (1 + Λ) := log_nonneg (by linarith)
    positivity
  | succ n =>
    have hpair := bond_site_sum_lower n
      (w := fun j ↦ S.K j ^ (-γ)) (g := energyWeight S γ)
      (A := driftAverage S σ) (I := impulseAverage S σ) (c := c) (d := d)
      (gap := S.gap) (mass := fun j ↦ S.mass (j + 1)) (T := sqrt Λ)
      (fun _ hj ↦ driftAverage_pos S hgraph hj)
      (fun _ hj ↦ impulseAverage_pos S hgraph hj) hc hd
      (fun _ hj ↦ (energyWeight_bounds S hγ.le hj).1.le)
      (fun _ hj ↦ energyWeight_le_before S hγ.le hj)
      (fun _ hj ↦ energyWeight_succ_le S hγ.le (by omega)) hgap hmass
    have hcosteq : (∑ j ∈ range (n + 1),
        (S.K j ^ (-γ) * driftAverage S σ j * S.gap j +
          energyWeight S γ j * impulseAverage S σ j * S.mass (j + 1))) =
        ∑ j ∈ range (n + 1), (S.K j ^ (-γ) * driftIntegral S σ j +
          energyWeight S γ j * impulseIntegral S σ j) := by
      apply sum_congr rfl
      intro j hj
      dsimp [driftAverage, impulseAverage]
      field_simp [(S.gap_pos j (mem_range.mp hj)).ne',
        (S.mass_pos (j + 1) (by have := mem_range.mp hj; omega)).ne']
    rw [hcosteq] at hpair
    have hbudget := mul_le_mul_of_nonneg_left (integrated_cost_budget S hγ hgraph) (sqrt_nonneg Λ)
    have hbracket := log_pair_bracket n (g := energyWeight S γ)
      (δ := driftLog S) (k := energyLog S) (q := slopeLog S)
      (A := driftAverage S σ) (I := impulseAverage S σ) hB₀
      (fun _ hj ↦ (energyWeight_bounds S hγ.le hj).1.le)
      (log_bounds S (by omega : 0 < n + 1)).1.le
      (fun _ hj ↦ bond_average_log_bound S hgraph hB hj)
      (fun _ hj ↦ site_average_log_bound S hgraph hB (by omega))
    have hprinted : 4 * (∑ j ∈ range (n + 1), energyWeight S γ j) -
        2 * energyWeight S γ 0 -
        ((1 + B) * weightedSum S γ (driftLog S) + B * weightedSum S γ (energyLog S) +
          (1 - B) * weightedSum S γ (slopeLog S)) ≤
        2 * sqrt Λ * feedbackValue γ σ 1 := by
      exact hbracket.trans (hpair.trans (by nlinarith only [hbudget]))
    exact finite_bound_algebra hB₀ (energyWeight_bounds S hγ.le (by omega : 0 < n + 1)).2
      le_rfl hprinted (weighted_driftLog_le S hγ.le hΛ hprod)
      (weighted_slopeLog_nonneg S hγ.le) (weighted_energyLog_le S hγ)

/-- The sharp source bound for a genuine finite string under its actual
spectral constraint. The top impedances are constructed from that operator;
no desired impedance or one-step certificate is a hypothesis. -/
theorem sharp_upper {γ B Λ : ℝ} {σ : ℝ → ℝ}
    (hγ : 0 < γ) (hB₀ : 0 ≤ B) (hΛ : S.spectralRadius < Λ)
    (hgraph : ∀ r ≥ 1, FeedbackGraphAt γ σ r)
    (hB : ∀ r ≥ 1, 0 ≤ logSlope σ r ∧ logSlope σ r ≤ B) :
    (∑ j ∈ range N, S.K (j + 1) ^ (-γ)) ≤
      sqrt Λ * feedbackValue γ σ 1 / 2 + (1 + B) / 4 * log (1 + Λ) +
        1 / 2 + (1 + 2 * B) / (4 * γ) := by
  obtain ⟨c, d, hpos, hgap, hmass⟩ := S.exists_top_impedances hΛ
  have hΛp : 0 < Λ := lt_of_le_of_lt (norm_nonneg S.operator) hΛ
  apply sharp_upper_of_impedances S hγ hB₀ hΛp hgraph hB
    (fun j hj ↦ (S.top_gap_mass hΛ j hj).le) c d
    (fun j hj ↦ (hpos j hj).1) (fun j hj ↦ (hpos j hj).2) ?_ hmass
  intro j hj
  simpa only [one_div] using hgap j hj

/-- The strict top parameter is removed by continuity. This is the literal
finite-κ estimate when the actual operator norm is at most `κ−1`. -/
theorem sharp_upper_of_spectralRadius_le {γ B R : ℝ} {σ : ℝ → ℝ}
    (hγ : 0 < γ) (hB₀ : 0 ≤ B) (hR : S.spectralRadius ≤ R)
    (hgraph : ∀ r ≥ 1, FeedbackGraphAt γ σ r)
    (hB : ∀ r ≥ 1, 0 ≤ logSlope σ r ∧ logSlope σ r ≤ B) :
    (∑ j ∈ range N, S.K (j + 1) ^ (-γ)) ≤
      sqrt R * feedbackValue γ σ 1 / 2 + (1 + B) / 4 * log (1 + R) +
        1 / 2 + (1 + 2 * B) / (4 * γ) := by
  have hR₀ : 0 ≤ R := (norm_nonneg S.operator).trans hR
  have hRn : 1 + R ≠ 0 := by linarith
  have hc : ContinuousAt (fun Λ : ℝ ↦
      sqrt Λ * feedbackValue γ σ 1 / 2 + (1 + B) / 4 * log (1 + Λ) +
        1 / 2 + (1 + 2 * B) / (4 * γ)) R := by fun_prop
  have hlim := hc.tendsto.mono_left (show nhdsWithin R (Set.Ioi R) ≤ nhds R from
    nhdsWithin_le_nhds)
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with Λ hΛ
  exact sharp_upper S hγ hB₀ (hR.trans_lt hΛ) hgraph hB

end DiscreteString
end
end krylov.Asymptotics
