import polyak.ModeLocking.TwoLag.ExactData
import polyak.ModeLocking.Regular.Endpoints

/-! The symmetric six-lag perturbation has exactly vanishing value and
first jet on the period grid. -/
noncomputable section
namespace polyak.ModeLocking.TwoLag
open General Levels Set Filter
open scoped Topology

def lift (q : Tuning) (s : ℝ) (K L : ℕ) : ℝ→ℝ :=
  finiteSymbol q s (pinLags K L) (pinWeight K 0 0 1)

theorem pin_extension_identity {K L : ℕ} (hK : 2≤K) (hL : K+2≤L)
    (q : Tuning) (s a b ε x : ℝ) :
    finiteSymbol q s (pinLags K L) (pinWeight K a b ε) x =
      extension q s K a b x+ε*lift q s K L x := by
  unfold lift finiteSymbol
  rw [pinWeight_sum hK hL, pinWeight_sum hK hL]
  unfold extension
  ring

theorem analyticAt_lift (q : Tuning) (s : ℝ) (K L : ℕ) {x : ℝ}
    (hx : x∈Icc 0 Real.pi) : AnalyticAt ℝ (lift q s K L) x :=
  analyticAt_finiteSymbol q s _ _ hx

theorem lift_zero_endpoint (q : Tuning) (s : ℝ) (K L : ℕ) : lift q s K L 0=0 := by
  change finiteSymbol q s _ _ (frequencyZero : ℝ)=0
  rw [finiteSymbol_actual]
  simp only [Curve.lag_at_zero, mul_zero, Finset.sum_const_zero]

theorem lift_slope_endpoint (q : Tuning) (s : ℝ) (K L : ℕ) :
    deriv (lift q s K L) 0=0 := finiteSymbol_deriv_zero q s _ _

theorem lift_grid_zero {K L : ℕ} (hK : 2≤K) (hL : K+2≤L)
    (q : Tuning) (s : ℝ) {ω : Frequency} (hω : ω∈periodicGrid L) :
    lift q s K L ω=0 := by
  rw [lift, pinning_grid_value hK hL q s 0 0 1 ω hω]
  ring

theorem lift_grid_slope {K L : ℕ} (hK : 2≤K) (hL : K+2≤L)
    (q : Tuning) (s : ℝ) {ω : Frequency} (hω : ω∈periodicGrid L) :
    deriv (lift q s K L) ω=0 := by
  unfold lift finiteSymbol
  rw [deriv_fun_sum (fun n _=>
    (analyticAt_lagExtension q s n ω.property).differentiableAt.const_mul _)]
  simp only [deriv_const_mul_field]
  rw [pinWeight_sum hK hL]
  have hθ := (analyticAt_phase q s ω.property).differentiableAt.hasDerivAt
  have h1 := symmetric_grid_jet hθ hω 1
  have hK := symmetric_grid_jet hθ hω (-(K : ℤ))
  change deriv (lagExtension q s (1+(L : ℤ))) ω+
    deriv (lagExtension q s (1-(L : ℤ))) ω-2*deriv (lagExtension q s 1) ω=0 at h1
  change deriv (lagExtension q s (-(K : ℤ)+(L : ℤ))) ω+
    deriv (lagExtension q s (-(K : ℤ)-(L : ℤ))) ω-2*deriv (lagExtension q s (-(K : ℤ))) ω=0 at hK
  change 0*deriv (lagExtension q s 1) ω+0*deriv (lagExtension q s (-(K : ℤ))) ω+
    1*(_+_-2*_+_+_-2*_)=0
  simp only [zero_mul, zero_add, one_mul]
  linear_combination h1+hK

end polyak.ModeLocking.TwoLag
