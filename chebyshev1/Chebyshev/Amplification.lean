import chebyshev1.Chebyshev.Normalization
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
Article: chebyshev1, Remark 5.5.
Exact finite amplification, with no large-condition-number approximation.
Use: `chebyshev1.SpectralInterval.amplification_accelerated_le` feeds
`chebyshev1.SpectralInterval.amplification_effectiveKappa_le` (amplification effective Kappa
le).
Proof chain: `chebyshev1.SpectralInterval.amplification_effectiveKappa_le` — chebyshev1,
Remark 5.5; Exact drift scale, accuracy asymptotics and rational finite examples.
-/
namespace chebyshev1
noncomputable section
open Polynomial Polynomial.Chebyshev

/--
The identity behind the exact amplification formula in Remark 5.5.

Exact identity `Real.cosh (2 * Real.arsinh (Real.sqrt u)) = 1 + 2*u`.

Use: `chebyshev1.chebyshev_arsinh` rewrites with this identity to establish the identity
`(T ℝ N).eval (1 + 2*u) = Real.cosh (2*(N:ℝ)*Real.arsinh (Real.sqrt u))`.

Article: chebyshev1, Remark 5.5 via `chebyshev1.SpectralInterval.amplification_cosh`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem cosh_two_arsinh_sqrt (u : ℝ) (hu : 0 ≤ u) :
    Real.cosh (2 * Real.arsinh (Real.sqrt u)) = 1 + 2*u := by
  rw [two_mul, Real.cosh_add, Real.cosh_arsinh, Real.sinh_arsinh]
  nlinarith [Real.sq_sqrt hu,
    Real.sq_sqrt (show 0 ≤ 1 + Real.sqrt u ^ 2 by positivity)]

/--
Exact identity `(T ℝ N).eval (1 + 2*u) = Real.cosh (2*(N:ℝ)*Real.arsinh (Real.sqrt u))`.

Use: `chebyshev1.SpectralInterval.amplification_cosh` rewrites with this identity to
establish exact identity `I.epsilon N * (T ℝ N).eval (1+2*delta/I.delta) = Real.cosh
(2*(N:ℝ)*Real.arsinh (Real.sqrt (delta/I.delta))) / Real.cosh (2*(N:ℝ)*Real.arsinh (Real.sqrt
(I.mu/I.delta)))`.

Article: chebyshev1, Remark 5.5 via `chebyshev1.SpectralInterval.amplification_cosh`.

Proof: Use the identities/estimates `chebyshev1.cosh_two_arsinh_sqrt` with the arguments
shown in the proof.
-/
theorem chebyshev_arsinh (N : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    (T ℝ N).eval (1 + 2*u) = Real.cosh (2*(N:ℝ)*Real.arsinh (Real.sqrt u)) := by
  rw [← cosh_two_arsinh_sqrt u hu, T_real_cosh]
  congr 1
  push_cast
  ring

/--
A lower secant bound for arsinh on a nonnegative interval.

The stated quantitative bound `(y-x) / Real.sqrt (1+y^2) ≤ Real.arsinh y - Real.arsinh x`.

Use: `chebyshev1.SpectralInterval.arsinh_gap_lower` uses this bound to establish the stated
quantitative bound `(Real.sqrt I.mu - Real.sqrt delta) / Real.sqrt I.L ≤ Real.arsinh (Real.sqrt
(I.mu/I.delta)) - Real.arsinh (Real.sqrt (delta/I.delta))`.

Article: chebyshev1, Remark 5.5 via
`chebyshev1.SpectralInterval.amplification_effectiveKappa_le`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem arsinh_sub_lower {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    (y-x) / Real.sqrt (1+y^2) ≤ Real.arsinh y - Real.arsinh x := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  have hs := (convex_Icc x y).mul_sub_le_image_sub_of_le_deriv
    Real.continuous_arsinh.continuousOn Real.differentiable_arsinh.differentiableOn
    (C := (Real.sqrt (1+y^2))⁻¹)
    (by
      intro t ht
      have ht' : t ∈ Set.Icc x y := interior_subset ht
      rw [(Real.hasDerivAt_arsinh t).deriv]
      apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
      apply Real.sqrt_le_sqrt
      nlinarith [ht'.1, ht'.2])
    x (Set.left_mem_Icc.mpr hxy) y (Set.right_mem_Icc.mpr hxy) hxy
  simpa only [div_eq_mul_inv, mul_comm] using hs

/--
The stated quantitative bound `Real.cosh a / Real.cosh b ≤ 2 * Real.exp (a-b)`.

Use: `chebyshev1.SpectralInterval.amplification_exp_le` uses this bound to establish the
stated quantitative bound `I.epsilon N * (T ℝ N).eval (1+2*delta/I.delta) ≤ 2 * Real.exp
(-2*(N:ℝ)*(Real.sqrt I.mu-Real.sqrt delta)/Real.sqrt I.L)`.

Article: chebyshev1, Remark 5.5 via
`chebyshev1.SpectralInterval.amplification_effectiveKappa_le`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem cosh_ratio_le_exp {a b : ℝ} (ha : 0 ≤ a) :
    Real.cosh a / Real.cosh b ≤ 2 * Real.exp (a-b) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hn : Real.exp (-a) ≤ Real.exp a := Real.exp_le_exp.mpr (by linarith)
  have hc : Real.cosh a ≤ Real.exp a := by rw [Real.cosh_eq]; linarith
  have hd : Real.exp b / 2 ≤ Real.cosh b := by
    rw [Real.cosh_eq]; linarith [Real.exp_pos (-b)]
  rw [div_le_iff₀ (Real.cosh_pos b), Real.exp_sub]
  have hmul := mul_le_mul_of_nonneg_left hd
    (show 0 ≤ 2*(Real.exp a/Real.exp b) by positivity)
  have he : 2*(Real.exp a/Real.exp b)*(Real.exp b/2) = Real.exp a := by
    field_simp
  linarith

namespace SpectralInterval

/--
Exact identity `I.eta = 1 + 2*I.mu/I.delta`.

Use: `chebyshev1.SpectralInterval.epsilon_cosh` rewrites with this identity to establish
exact identity `I.epsilon N = 1 / Real.cosh (2*(N:ℝ)*Real.arsinh (Real.sqrt (I.mu/I.delta)))`.

Article: chebyshev1, Remark 5.5 via `chebyshev1.SpectralInterval.drift_factor_limit`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem eta_eq_one_add (I : SpectralInterval) : I.eta = 1 + 2*I.mu/I.delta := by
  dsimp [eta, delta]
  field_simp [ne_of_gt (sub_pos.mpr I.mu_lt_L)]
  ring

/--
Exact identity `I.epsilon N = 1 / Real.cosh (2*(N:ℝ)*Real.arsinh (Real.sqrt (I.mu/I.delta)))`.

Use: `chebyshev1.SpectralInterval.amplification_cosh` rewrites with this identity to
establish exact identity `I.epsilon N * (T ℝ N).eval (1+2*delta/I.delta) = Real.cosh
(2*(N:ℝ)*Real.arsinh (Real.sqrt (delta/I.delta))) / Real.cosh (2*(N:ℝ)*Real.arsinh (Real.sqrt
(I.mu/I.delta)))`.

Article: chebyshev1, Remark 5.5 via `chebyshev1.SpectralInterval.amplification_cosh`.

Proof: Use the identities/estimates `chebyshev1.SpectralInterval.eta_eq_one_add`,
`chebyshev1.chebyshev_arsinh`, `chebyshev1.SpectralInterval.delta_pos` with the
arguments shown in the proof.
-/
theorem epsilon_cosh (I : SpectralInterval) (N : ℕ) :
    I.epsilon N = 1 / Real.cosh (2*(N:ℝ)*Real.arsinh (Real.sqrt (I.mu/I.delta))) := by
  unfold epsilon den
  rw [I.eta_eq_one_add]
  rw [show 2*I.mu/I.delta = 2*(I.mu/I.delta) by ring,
    chebyshev_arsinh N _ (div_nonneg I.mu_pos.le I.delta_pos.le)]

/--
Exact finite amplification, with no large-condition-number approximation.

Exact identity `I.epsilon N * (T ℝ N).eval (1+2*delta/I.delta) = Real.cosh (2*(N:ℝ)*Real.arsinh
(Real.sqrt (delta/I.delta))) / Real.cosh (2*(N:ℝ)*Real.arsinh (Real.sqrt (I.mu/I.delta)))`.

Use: `chebyshev1.SpectralInterval.amplification_exp_le` rewrites with this identity to
establish the stated quantitative bound `I.epsilon N * (T ℝ N).eval (1+2*delta/I.delta) ≤ 2 *
Real.exp (-2*(N:ℝ)*(Real.sqrt I.mu-Real.sqrt delta)/Real.sqrt I.L)`.

Article: chebyshev1, Remark 5.5.

Proof: Use the identities/estimates `chebyshev1.SpectralInterval.epsilon_cosh`,
`chebyshev1.chebyshev_arsinh`, `chebyshev1.SpectralInterval.delta_pos` with the
arguments shown in the proof.
-/
theorem amplification_cosh (I : SpectralInterval) (N : ℕ) (delta : ℝ) (hd : 0 ≤ delta) :
    I.epsilon N * (T ℝ N).eval (1+2*delta/I.delta) =
      Real.cosh (2*(N:ℝ)*Real.arsinh (Real.sqrt (delta/I.delta))) /
        Real.cosh (2*(N:ℝ)*Real.arsinh (Real.sqrt (I.mu/I.delta))) := by
  -- Use the identities/estimates `chebyshev1.SpectralInterval.epsilon_cosh`,
  -- `chebyshev1.chebyshev_arsinh`, `chebyshev1.SpectralInterval.delta_pos` with the
  -- arguments shown in the proof.
  rw [I.epsilon_cosh,
    show 2*delta/I.delta = 2*(delta/I.delta) by ring,
    chebyshev_arsinh N _ (div_nonneg hd I.delta_pos.le)]
  ring

/--
The stated quantitative bound `(Real.sqrt I.mu - Real.sqrt delta) / Real.sqrt I.L ≤ Real.arsinh
(Real.sqrt (I.mu/I.delta)) - Real.arsinh (Real.sqrt (delta/I.delta))`.

Use: `chebyshev1.SpectralInterval.amplification_exp_le` uses this bound to establish the
stated quantitative bound `I.epsilon N * (T ℝ N).eval (1+2*delta/I.delta) ≤ 2 * Real.exp
(-2*(N:ℝ)*(Real.sqrt I.mu-Real.sqrt delta)/Real.sqrt I.L)`.

Article: chebyshev1, Remark 5.5 via
`chebyshev1.SpectralInterval.amplification_effectiveKappa_le`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem arsinh_gap_lower (I : SpectralInterval) (delta : ℝ) (hd : 0 ≤ delta)
    (hdmu : delta ≤ I.mu) :
    (Real.sqrt I.mu - Real.sqrt delta) / Real.sqrt I.L ≤
      Real.arsinh (Real.sqrt (I.mu/I.delta)) -
        Real.arsinh (Real.sqrt (delta/I.delta)) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hb := arsinh_sub_lower (Real.sqrt_nonneg (delta/I.delta))
    (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hdmu I.delta_pos.le))
  have he : 1 + Real.sqrt (I.mu/I.delta)^2 = I.L/I.delta := by
    rw [Real.sq_sqrt (div_nonneg I.mu_pos.le I.delta_pos.le)]
    dsimp [SpectralInterval.delta]
    field_simp [ne_of_gt (sub_pos.mpr I.mu_lt_L)]
    ring
  rw [he, Real.sqrt_div I.mu_pos.le, Real.sqrt_div hd,
    Real.sqrt_div (show 0 ≤ I.L by linarith [I.mu_pos, I.mu_lt_L])] at hb
  rw [Real.sqrt_div I.mu_pos.le, Real.sqrt_div hd]
  convert hb using 1
  field_simp [ne_of_gt (Real.sqrt_pos.mpr I.delta_pos),
    ne_of_gt (Real.sqrt_pos.mpr (show 0 < I.L by linarith [I.mu_pos, I.mu_lt_L]))]

/--
The stated quantitative bound `I.epsilon N * (T ℝ N).eval (1+2*delta/I.delta) ≤ 2 * Real.exp
(-2*(N:ℝ)*(Real.sqrt I.mu-Real.sqrt delta)/Real.sqrt I.L)`.

Use: `chebyshev1.SpectralInterval.amplification_accelerated_le` uses this bound to
establish the stated quantitative bound `I.epsilon N * (T ℝ N).eval (1+2*delta/I.delta) ≤
2*Real.exp (-2*(N:ℝ)/Real.sqrt I.kappa * (1-Real.sqrt (delta/I.mu)))`.

Article: chebyshev1, Remark 5.5 via
`chebyshev1.SpectralInterval.amplification_effectiveKappa_le`.

Proof: Use the identities/estimates `chebyshev1.SpectralInterval.amplification_cosh`,
`chebyshev1.cosh_ratio_le_exp`, `chebyshev1.SpectralInterval.arsinh_gap_lower` with the
arguments shown in the proof.
-/
theorem amplification_exp_le (I : SpectralInterval) (N : ℕ) (delta : ℝ)
    (hd : 0 ≤ delta) (hdmu : delta ≤ I.mu) :
    I.epsilon N * (T ℝ N).eval (1+2*delta/I.delta) ≤
      2 * Real.exp (-2*(N:ℝ)*(Real.sqrt I.mu-Real.sqrt delta)/Real.sqrt I.L) := by
  -- Use the identities/estimates `chebyshev1.SpectralInterval.amplification_cosh`,
  -- `chebyshev1.cosh_ratio_le_exp`, `chebyshev1.SpectralInterval.arsinh_gap_lower`
  -- with the arguments shown in the proof.
  rw [I.amplification_cosh N delta hd]
  have hN : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
  refine (cosh_ratio_le_exp (by
    apply mul_nonneg (by positivity)
    exact Real.arsinh_nonneg_iff.mpr (Real.sqrt_nonneg _))).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  have hb := mul_le_mul_of_nonneg_left (I.arsinh_gap_lower delta hd hdmu)
    (show 0 ≤ 2*(N:ℝ) by positivity)
  ring_nf at hb ⊢
  linarith

/--
Defines `kappa` of type `ℝ` by `I.L/I.mu`.

Use: `chebyshev1.SpectralInterval.drift_exponent_eq` rewrites with this definition to
establish exact identity `-2*(N:ℝ)*(Real.sqrt I.mu-Real.sqrt delta)/Real.sqrt I.L =
-2*(N:ℝ)/Real.sqrt I.kappa * (1-Real.sqrt (delta/I.mu))`.

Article: chebyshev1, Remark 5.5 via
`chebyshev1.SpectralInterval.amplification_effectiveKappa_le`.
-/
def kappa (I : SpectralInterval) : ℝ := I.L/I.mu

/--
Exact identity `-2*(N:ℝ)*(Real.sqrt I.mu-Real.sqrt delta)/Real.sqrt I.L = -2*(N:ℝ)/Real.sqrt
I.kappa * (1-Real.sqrt (delta/I.mu))`.

Use: `chebyshev1.SpectralInterval.amplification_accelerated_le` rewrites with this identity
to prove the bound `I.epsilon N * (T ℝ N).eval (1+2*delta/I.delta) ≤
2*Real.exp (-2*(N:ℝ)/Real.sqrt I.kappa * (1-Real.sqrt (delta/I.mu)))`.

Article: chebyshev1, Remark 5.5 via
`chebyshev1.SpectralInterval.amplification_effectiveKappa_le`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem drift_exponent_eq (I : SpectralInterval) (N : ℕ) (delta : ℝ) (hd : 0 ≤ delta) :
    -2*(N:ℝ)*(Real.sqrt I.mu-Real.sqrt delta)/Real.sqrt I.L =
      -2*(N:ℝ)/Real.sqrt I.kappa * (1-Real.sqrt (delta/I.mu)) := by
  rw [kappa, Real.sqrt_div (show 0 ≤ I.L by linarith [I.mu_pos, I.mu_lt_L]),
    Real.sqrt_div hd]
  field_simp [ne_of_gt (Real.sqrt_pos.mpr I.mu_pos),
    ne_of_gt (Real.sqrt_pos.mpr (show 0 < I.L by linarith [I.mu_pos, I.mu_lt_L]))]

/--
The stated quantitative bound `I.epsilon N * (T ℝ N).eval (1+2*delta/I.delta) ≤ 2*Real.exp
(-2*(N:ℝ)/Real.sqrt I.kappa * (1-Real.sqrt (delta/I.mu)))`.

Use: `chebyshev1.SpectralInterval.amplification_effectiveKappa_le` uses this bound to
establish the stated quantitative bound `I.epsilon N*(T ℝ N).eval (1+2*delta/I.delta) ≤ 2*exp
(-2*(N:ℝ)/sqrt (I.effectiveKappa delta))`.

Article: chebyshev1, Remark 5.5 via
`chebyshev1.SpectralInterval.amplification_effectiveKappa_le`.

Proof: Use the identities/estimates `chebyshev1.SpectralInterval.drift_exponent_eq`,
`chebyshev1.SpectralInterval.amplification_exp_le` with the arguments shown in the proof.
-/
theorem amplification_accelerated_le (I : SpectralInterval) (N : ℕ) (delta : ℝ)
    (hd : 0 ≤ delta) (hdmu : delta ≤ I.mu) :
    I.epsilon N * (T ℝ N).eval (1+2*delta/I.delta) ≤
      2*Real.exp (-2*(N:ℝ)/Real.sqrt I.kappa * (1-Real.sqrt (delta/I.mu))) := by
  rw [← I.drift_exponent_eq N delta hd]
  exact I.amplification_exp_le N delta hd hdmu

/--
Exact identity `(I.residual N).eval 0 = 1`.

Use: `chebyshev1.Realization.static_shift_at_mu` rewrites with this identity to establish
exact identity `opNorm (R.operatorTransfer N (fun _ => scalarMatrix (I.mu-I.mu))) = 1`.

Article: chebyshev1, Remark 5.5 via `chebyshev1.Realization.static_shift_at_mu`.

Proof: Use the identities/estimates `chebyshev1.SpectralInterval.residual_eval`,
`chebyshev1.SpectralInterval.den_ne` with the arguments shown in the proof.
-/
@[simp] theorem residual_eval_zero (I : SpectralInterval) (N : ℕ) :
    (I.residual N).eval 0 = 1 := by
  have hz : I.z 0 = I.eta := by simp [z, eta]
  rw [I.residual_eval, hz]
  exact div_self (I.den_ne N)

end SpectralInterval
end
end chebyshev1
