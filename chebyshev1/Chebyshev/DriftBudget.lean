import chebyshev1.Chebyshev.Amplification
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Algebra.Order.Floor.Semiring

/-! Exact finite drift budgets and the least integer accuracy horizon. -/
namespace chebyshev1.SpectralInterval
noncomputable section
open Polynomial Polynomial.Chebyshev Real

/-- The largest drift compatible with a prescribed amplification. -/
def driftBudget (I : SpectralInterval) (N : ℕ) (M : ℝ) : ℝ :=
  I.delta * sinh (arcosh M / (2 * (N : ℝ))) ^ 2

/-- A finite, exact drift budget, including the unit-amplification endpoint. -/
theorem amplification_le_iff_driftBudget (I : SpectralInterval)
    {N : ℕ} (hN : 0 < N) {delta M : ℝ} (hd : 0 ≤ delta) (hM : 1 ≤ M) :
    (T ℝ N).eval (1 + 2 * delta / I.delta) ≤ M ↔
      delta ≤ I.driftBudget N M := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hu : 0 ≤ delta / I.delta := div_nonneg hd I.delta_pos.le
  have ha : 0 ≤ arcosh M := arcosh_nonneg hM
  have hb : 0 ≤ arsinh (sqrt (delta / I.delta)) :=
    arsinh_nonneg_iff.mpr (sqrt_nonneg _)
  have ht : 0 ≤ arcosh M / (2 * (N : ℝ)) := by positivity
  have hs : 0 ≤ sinh (arcosh M / (2 * (N : ℝ))) := sinh_nonneg_iff.mpr ht
  conv_lhs =>
    rw [show 1 + 2 * delta / I.delta = 1 + 2 * (delta / I.delta) by ring,
      chebyshev_arsinh N _ hu]
    rhs
    rw [← cosh_arcosh hM]
  rw [cosh_le_cosh,
    abs_of_nonneg (show 0 ≤ 2 * (N : ℝ) * arsinh (sqrt (delta / I.delta)) by positivity),
    abs_of_nonneg ha]
  have hdiv : 2 * (N : ℝ) * arsinh (sqrt (delta / I.delta)) ≤ arcosh M ↔
      arsinh (sqrt (delta / I.delta)) ≤ arcosh M / (2 * (N : ℝ)) := by
    rw [le_div_iff₀ (show 0 < 2 * (N : ℝ) by positivity)]
    ring_nf
  rw [hdiv]
  have hinv : arsinh (sqrt (delta / I.delta)) ≤ arcosh M / (2 * (N : ℝ)) ↔
      sqrt (delta / I.delta) ≤ sinh (arcosh M / (2 * (N : ℝ))) := by
    conv_lhs => rhs; rw [← arsinh_sinh (arcosh M / (2 * (N : ℝ)))]
    exact arsinh_le_arsinh
  rw [hinv]
  constructor
  · intro h
    have hsq := mul_self_le_mul_self (sqrt_nonneg (delta / I.delta)) h
    rw [← pow_two, sq_sqrt hu] at hsq
    have := (div_le_iff₀ I.delta_pos).mp hsq
    simpa [driftBudget, pow_two, mul_comm] using this
  · intro h
    have hsq : delta / I.delta ≤ sinh (arcosh M / (2 * (N : ℝ))) ^ 2 := by
      apply (div_le_iff₀ I.delta_pos).mpr
      simpa [driftBudget, mul_comm] using h
    nlinarith [sq_sqrt hu, sqrt_nonneg (delta / I.delta)]

/-- The inverse-hyperbolic expression for the spectral normalization. -/
theorem arcosh_eta (I : SpectralInterval) :
    arcosh I.eta = 2 * arsinh (sqrt (I.mu / I.delta)) := by
  have hu : 0 ≤ I.mu / I.delta := div_nonneg I.mu_pos.le I.delta_pos.le
  rw [I.eta_eq_one_add, show 1 + 2 * I.mu / I.delta = 1 + 2 * (I.mu / I.delta) by ring,
    ← chebyshev1.cosh_two_arsinh_sqrt _ hu]
  exact arcosh_cosh (mul_nonneg (by norm_num) (arsinh_nonneg_iff.mpr (sqrt_nonneg _)))

/-- Least integer horizon for a specified unperturbed contraction. -/
def accuracyHorizon (I : SpectralInterval) (epsilon : ℝ) : ℕ :=
  ⌈arcosh (1 / epsilon) / arcosh I.eta⌉₊

theorem den_cosh_arcosh (I : SpectralInterval) (N : ℕ) :
    I.den N = cosh ((N : ℝ) * arcosh I.eta) := by
  rw [I.arcosh_eta]
  change (T ℝ N).eval I.eta = _
  rw [I.eta_eq_one_add, show 1 + 2 * I.mu / I.delta = 1 + 2 * (I.mu / I.delta) by ring,
    chebyshev_arsinh N _ (div_nonneg I.mu_pos.le I.delta_pos.le)]
  congr 1
  ring

/-- Both achievability and minimality of the rounded horizon, with explicit accuracy domain. -/
theorem accuracyHorizon_le_iff (I : SpectralInterval) {epsilon : ℝ}
    (he : 0 < epsilon) (he1 : epsilon < 1) (N : ℕ) :
    I.accuracyHorizon epsilon ≤ N ↔ I.epsilon N ≤ epsilon := by
  have ha : 0 < arcosh I.eta := arcosh_pos I.eta_gt_one
  have heinv : 1 ≤ 1 / epsilon := (le_div_iff₀ he).mpr (by linarith)
  have hb : 0 ≤ arcosh (1 / epsilon) := arcosh_nonneg heinv
  have hn : 0 ≤ (N : ℝ) * arcosh I.eta := by positivity
  rw [accuracyHorizon, Nat.ceil_le, div_le_iff₀ ha]
  have hc : arcosh (1 / epsilon) ≤ (N : ℝ) * arcosh I.eta ↔
      1 / epsilon ≤ cosh ((N : ℝ) * arcosh I.eta) := by
    conv_rhs => lhs; rw [← cosh_arcosh heinv]
    rw [cosh_le_cosh, abs_of_nonneg hb, abs_of_nonneg hn]
  rw [hc, SpectralInterval.epsilon, I.den_cosh_arcosh]
  rw [div_le_iff₀ he, div_le_iff₀ (cosh_pos _)]
  exact ⟨fun h => by nlinarith, fun h => by nlinarith⟩

theorem accuracyHorizon_pos (I : SpectralInterval) {epsilon : ℝ}
    (he : 0 < epsilon) (he1 : epsilon < 1) : 0 < I.accuracyHorizon epsilon := by
  apply Nat.pos_of_ne_zero
  intro h
  have hb := (I.accuracyHorizon_le_iff he he1 0).mp (by omega)
  have hz : I.epsilon 0 = 1 := by simp [SpectralInterval.epsilon, den]
  rw [hz] at hb
  linarith

theorem epsilon_accuracyHorizon_le (I : SpectralInterval) {epsilon : ℝ}
    (he : 0 < epsilon) (he1 : epsilon < 1) :
    I.epsilon (I.accuracyHorizon epsilon) ≤ epsilon :=
  (I.accuracyHorizon_le_iff he he1 _).mp le_rfl

end
end chebyshev1.SpectralInterval
