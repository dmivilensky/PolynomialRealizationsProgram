import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Tactic

/-!
Article: chebyshev1, Corollary 4.4.
The second-kind bound follows from mathlib's endpoint bound for derivatives of T.
Use: `chebyshev1.abs_U_eval_le` feeds `chebyshev1.Prefix.kernel_abs_le_endpoint` (kernel abs
le endpoint).
Proof chain: `chebyshev1.Prefix.gain_exact` — chebyshev1, Theorem 2.2; Exact prefix kernel,
gain and asymptotics.
Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval. The needed form is proved here.
-/
namespace chebyshev1

noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped Polynomial

/--
The spectral interval of the paper, including its strict hypotheses.

Use: `chebyshev1.SpectralInterval.z_mem` uses this record of data and proof obligations to
establish membership in the specified domain/enclosure: `I.z lam ∈ Set.Icc (-1) 1`.

Article: chebyshev1, Theorem 2.1 via `chebyshev1.Prefix.residualPolynomial_eq`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.
-/
structure SpectralInterval where
  /-- Strictly positive lower spectral endpoint. -/
  mu : ℝ
  /-- Upper spectral endpoint; it is strictly larger than mu. -/
  L : ℝ
  /-- Positivity needed for the outside-spectrum Chebyshev normalization and denominators. -/
  mu_pos : 0 < mu
  /-- Nondegeneracy of the spectral interval, ensuring the affine spectral coordinate is defined. -/
  mu_lt_L : mu < L

namespace SpectralInterval

variable (I : SpectralInterval)

/--
Defines `delta` of type `ℝ` by `I.L - I.mu`.

Use: `chebyshev1.SpectralInterval.z_mem` uses this definition to establish membership in
the specified domain/enclosure: `I.z lam ∈ Set.Icc (-1) 1`.

Article: chebyshev1, Theorem 2.2 via `chebyshev1.Prefix.kernel_zero`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.
-/
def delta : ℝ := I.L - I.mu
/--
Defines `eta` of type `ℝ` by `(I.L + I.mu) / I.delta`.

Use: `chebyshev1.SpectralInterval.den` uses this definition in the displayed construction
of `den`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev1, Theorem 2.2 via `chebyshev1.Prefix.kernel_zero`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.
-/
def eta : ℝ := (I.L + I.mu) / I.delta
/--
Defines `z` of type `ℝ` by `(I.L + I.mu - 2 * lam) / I.delta`.

Use: `chebyshev1.SpectralInterval.z_eq` uses this definition to establish the identity
`I.z lam = I.eta - 2 / I.delta * lam`.

Article: chebyshev1, Theorem 2.2 via `chebyshev1.Prefix.kernel_zero`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.
-/
def z (lam : ℝ) : ℝ := (I.L + I.mu - 2 * lam) / I.delta
/--
Defines `den` of type `ℝ` by `(T ℝ n).eval I.eta`.

Use: `chebyshev1.SpectralInterval.den_ne` uses this definition to establish the precise
assertion is `I.den n ≠ 0`.

Article: chebyshev1, Theorem 2.2 via `chebyshev1.Prefix.kernel_zero`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.
-/
def den (n : ℕ) : ℝ := (T ℝ n).eval I.eta
/--
Defines `residual` of type `ℝ[X]` by `Polynomial.C (I.den n)⁻¹ * (T ℝ n).comp (Polynomial.C
I.eta - Polynomial.C (2 / I.delta) * X)`.

Use: `chebyshev1.SpectralInterval.residual_eval` rewrites with this definition to establish
exact identity `(I.residual n).eval lam = (T ℝ n).eval (I.z lam) / I.den n`.

Article: chebyshev1, Theorem 2.1 via `chebyshev1.Prefix.residualPolynomial_eq`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.
-/
def residual (n : ℕ) : ℝ[X] :=
  Polynomial.C (I.den n)⁻¹ * (T ℝ n).comp
    (Polynomial.C I.eta - Polynomial.C (2 / I.delta) * X)
/--
Defines `epsilon` of type `ℝ` by `1 / I.den n`.

Use: `chebyshev1.JacobiData.opNorm_driftOrder_G_le` uses this definition to establish the
stated quantitative bound `opNorm (J.driftOrder I N k H E) ≤ I.epsilon N / 2 * (4 * delta /
I.delta)^k * J.G N k`.

Article: chebyshev1, Theorem 2.2 via `chebyshev1.Prefix.gain_exact`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.
-/
def epsilon (n : ℕ) : ℝ := 1 / I.den n

/--
The stated quantitative bound `0 < I.delta`.

Use: `chebyshev1.SpectralInterval.eta_gt_one` rewrites with this bound to establish the
stated quantitative bound `1 < I.eta`.

Article: chebyshev1, Theorem 2.2 via `chebyshev1.Prefix.kernel_zero`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem delta_pos : 0 < I.delta := sub_pos.mpr I.mu_lt_L
/--
The stated quantitative bound `0 < I.L + I.mu`.

Use: `chebyshev1.Prefix.gamma_succ` uses this bound to establish the identity `gamma I (t
+ 1) = (1 + beta I (t + 1)) * (2 / (I.L + I.mu))`.

Article: chebyshev1, Theorem 2.2 via `chebyshev1.Prefix.kernel_zero`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem sum_pos : 0 < I.L + I.mu := by linarith [I.mu_pos, I.mu_lt_L]
/--
The stated quantitative bound `1 < I.eta`.

Use: `chebyshev1.SpectralInterval.den_pos` uses this bound to establish the stated
quantitative bound `0 < I.den n`.

Article: chebyshev1, Theorem 2.2 via `chebyshev1.Prefix.gain_exact`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.

Proof: Use the identities/estimates `chebyshev1.SpectralInterval.delta_pos` with the
arguments shown in the proof.
-/
theorem eta_gt_one : 1 < I.eta := by
  rw [eta, lt_div_iff₀ I.delta_pos]
  dsimp [delta]
  linarith [I.mu_pos]
/--
The stated quantitative bound `0 < I.den n`.

Use: `chebyshev1.SpectralInterval.den_ne` uses this bound to establish the precise
assertion is `I.den n ≠ 0`.

Article: chebyshev1, Theorem 2.2 via `chebyshev1.Prefix.gain_exact`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.

Proof: Use the identities/estimates `chebyshev1.SpectralInterval.eta_gt_one` with the
arguments shown in the proof.
-/
theorem den_pos (n : ℕ) : 0 < I.den n :=
  lt_of_lt_of_le zero_lt_one (one_le_eval_T_real n I.eta_gt_one.le)
/--
The precise assertion is `I.den n ≠ 0`.

Use: `chebyshev1.Prefix.beta_coefficient` uses this assertion to establish the identity
`2 * I.eta * I.den (t + 1) / I.den (t + 2) = 1 + beta I (t + 1)`.

Article: chebyshev1, Theorem 2.2 via `chebyshev1.Prefix.kernel_zero`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.

Proof: Use the identities/estimates `chebyshev1.SpectralInterval.den_pos` with the
arguments shown in the proof.
-/
theorem den_ne (n : ℕ) : I.den n ≠ 0 := ne_of_gt (I.den_pos n)
/--
Exact identity `I.epsilon n = 1 / |I.den n|`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev1, Corollary 4.4.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.

Proof: Use the identities/estimates `chebyshev1.SpectralInterval.den_pos` with the
arguments shown in the proof.
-/
theorem epsilon_eq_abs (n : ℕ) : I.epsilon n = 1 / |I.den n| := by
  rw [abs_of_pos (I.den_pos n)]
  rfl
/--
Exact identity `I.den 0 = 1`.

Use: `chebyshev1.Prefix.jacobi_b_succ` rewrites with this identity to establish exact
identity `(jacobiData.method I).b (n + 1) = -(I.den n / I.den (n + 2))`.

Article: chebyshev1, Theorem 2.1 via `chebyshev1.Prefix.residualPolynomial_eq`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[simp] theorem den_zero : I.den 0 = 1 := by simp [den]
/--
Exact identity `I.den 1 = I.eta`.

Use: `chebyshev1.Prefix.kernel_zero` rewrites with this identity to establish exact
identity `(realization I).kernel N 0 lam nu = -(2 / (I.delta * I.den N)) * (U ℝ (N - 1)).eval
(I.z lam)`.

Article: chebyshev1, Theorem 2.2 via `chebyshev1.Prefix.kernel_zero`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[simp] theorem den_one : I.den 1 = I.eta := by simp [den]
/--
Exact identity `I.den (n + 2) = 2 * I.eta * I.den (n + 1) - I.den n`.

Use: `chebyshev1.Prefix.beta_coefficient` uses this identity to establish the identity `2
* I.eta * I.den (t + 1) / I.den (t + 2) = 1 + beta I (t + 1)`.

Article: chebyshev1, Theorem C.1 via `chebyshev1.TwoTerm.local_unique`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem den_add_two (n : ℕ) :
    I.den (n + 2) = 2 * I.eta * I.den (n + 1) - I.den n := by
  simp [den, Nat.cast_add, T_add_two]
/--
Exact identity `I.z lam = I.eta - 2 / I.delta * lam`.

Use: `chebyshev1.SpectralInterval.residual_eval` rewrites with this identity to establish
exact identity `(I.residual n).eval lam = (T ℝ n).eval (I.z lam) / I.den n`.

Article: chebyshev1, Theorem 2.1 via `chebyshev1.Prefix.residualPolynomial_eq`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem z_eq (lam : ℝ) : I.z lam = I.eta - 2 / I.delta * lam := by
  dsimp [z, eta]
  ring
/--
Exact identity `I.z I.mu = 1`.

Use:
`_private.chebyshev1.Chebyshev.EndpointDerivatives.0.chebyshev1.SpectralInterval.affine_eval_mu`
rewrites with this identity to establish the identity `I.eta - (2 / I.delta) * I.mu = 1`.

Article: chebyshev1, Theorem E.1 via `chebyshev1.SineJacobi.kernel_abs_le_endpoint`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.

Proof: Use the identities/estimates `chebyshev1.SpectralInterval.delta_pos` with the
arguments shown in the proof.
-/
@[simp] theorem z_mu : I.z I.mu = 1 := by
  dsimp [z]
  have h : I.L + I.mu - 2 * I.mu = I.delta := by dsimp [delta]; ring
  rw [h, div_self (ne_of_gt I.delta_pos)]
/--
Membership in the specified domain/enclosure: `I.z lam ∈ Set.Icc (-1) 1`.

Use: `chebyshev1.SpectralInterval.residual_abs_le` uses this assertion to establish the
stated quantitative bound `|(I.residual n).eval lam| ≤ I.epsilon n`.

Article: chebyshev1, Theorem E.1 via `chebyshev1.SineJacobi.kernel_abs_le_endpoint`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.

Proof: Use the identities/estimates `chebyshev1.SpectralInterval.delta_pos` with the
arguments shown in the proof.
-/
theorem z_mem {lam : ℝ} (h : lam ∈ Set.Icc I.mu I.L) :
    I.z lam ∈ Set.Icc (-1) 1 := by
  -- Use the identities/estimates `chebyshev1.SpectralInterval.delta_pos` with the
  -- arguments shown in the proof.
  constructor
  · rw [z, le_div_iff₀ I.delta_pos]
    dsimp [delta]
    linarith [h.2]
  · rw [z, div_le_iff₀ I.delta_pos]
    dsimp [delta]
    linarith [h.1]
/--
Exact identity `(I.residual n).eval lam = (T ℝ n).eval (I.z lam) / I.den n`.

Use: `chebyshev1.SpectralInterval.residual_abs_le` rewrites with this identity to establish
the stated quantitative bound `|(I.residual n).eval lam| ≤ I.epsilon n`.

Article: chebyshev1, Theorem 2.1 via `chebyshev1.Prefix.residualPolynomial_eq`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.

Proof: Use the identities/estimates `chebyshev1.SpectralInterval.z_eq` with the arguments
shown in the proof.
-/
theorem residual_eval (n : ℕ) (lam : ℝ) :
    (I.residual n).eval lam = (T ℝ n).eval (I.z lam) / I.den n := by simp [residual, Polynomial.eval_comp, z_eq, div_eq_mul_inv, mul_comm]

/--
The stated quantitative bound `|(I.residual n).eval lam| ≤ I.epsilon n`.

Use: `chebyshev1.opNorm_residual_le` uses this bound to establish the stated quantitative
bound `opNorm (aeval H (I.residual N)) ≤ I.epsilon N`.

Article: chebyshev1, Corollary 5.4 via `chebyshev1.Nonlinear.lipschitzHessian_error_le`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.

Proof: Use the identities/estimates `chebyshev1.SpectralInterval.residual_eval`,
`chebyshev1.SpectralInterval.den_pos`, `chebyshev1.SpectralInterval.z_mem` with the
arguments shown in the proof.
-/
theorem residual_abs_le (n : ℕ) {lam : ℝ} (h : lam ∈ Set.Icc I.mu I.L) :
    |(I.residual n).eval lam| ≤ I.epsilon n := by
  rw [I.residual_eval, abs_div, abs_of_pos (I.den_pos n)]
  exact div_le_div_of_nonneg_right (abs_eval_T_real_le_one n (abs_le.mpr (I.z_mem h)))
    (I.den_pos n).le

end SpectralInterval

/--
The second-kind bound follows from mathlib's endpoint bound for derivatives of T.

The stated quantitative bound `|(U ℝ n).eval x| ≤ n + 1`.

Use: `chebyshev1.Prefix.jacobiBlock_endpoint_max` uses this bound to establish the stated
quantitative bound `|(jacobiBlock a n).eval x| ≤ (jacobiBlock a n).eval 1`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem abs_U_eval_le (n : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    |(U ℝ n).eval x| ≤ n + 1 := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  have h := abs_iterate_derivative_T_real_le (n + 1) 1 hx
  simp only [Function.iterate_one] at h
  simp only [T_derivative_eq_U, add_sub_cancel_right, Polynomial.eval_mul,
    Polynomial.eval_intCast, U_eval_one] at h
  push_cast at h
  have hn : (0 : ℝ) < n + 1 := by positivity
  rw [abs_mul, abs_of_pos hn] at h
  nlinarith

end
end chebyshev1
