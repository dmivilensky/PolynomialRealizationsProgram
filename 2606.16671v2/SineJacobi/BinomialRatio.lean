import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic

/-!
Article: 2606.16671v2, Theorem E.3.
Wallis supplies the asymptotic normalization directly, without a new Stirling proof.
Use: `«2606.16671v2».SineJacobi.binomialRatio_scaled_limit` feeds
`«2606.16671v2».SineJacobi.ratio_scaled_limit` (The bulk ratio asymptotic, with arbitrary moving
sites and arbitrary index filters).
Proof chain: `«2606.16671v2».SineJacobi.ratio_scaled_limit` — 2606.16671v2, Theorem E.3; Hard-edge
recurrence, singular ODE, uniqueness and endpoint limits.
Source: mathlib, Mathlib.Analysis.SpecialFunctions.Trigonometric.Wallis — Wallis central-binomial
asymptotics. The needed form is proved here.
-/
namespace «2606.16671v2».SineJacobi
noncomputable section
open Filter Topology Real

/--
The limiting half-binomial ratio bₙ used in the endpoint asymptotics.

Use: `«2606.16671v2».SineJacobi.binomialRatio_eq_central` rewrites with this definition to
establish exact identity `binomialRatio n = (Nat.centralBinom n:ℝ)/(4:ℝ)^n`.

Article: 2606.16671v2, Theorem E.3 via `«2606.16671v2».SineJacobi.endpoint_global_bound`.

Source: mathlib, Mathlib.Analysis.SpecialFunctions.Trigonometric.Wallis — Wallis
central-binomial asymptotics.
-/
def binomialRatio : ℕ → ℝ
  | 0 => 1
  | n+1 => binomialRatio n * ((n:ℝ)+1/2)/((n:ℝ)+1)

/--
Exact identity `binomialRatio 0 = 1`.

Use: registered as a simplification rule for the displayed expression. The rule remains
available even when kernel reduction eliminates an explicit reference to this lemma.

Article: 2606.16671v2, Theorem E.3.

Source: mathlib, Mathlib.Analysis.SpecialFunctions.Trigonometric.Wallis — Wallis
central-binomial asymptotics.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
@[simp] theorem binomialRatio_zero : binomialRatio 0 = 1 := rfl

/--
The stated quantitative bound `0 < binomialRatio n`.

Use: `«2606.16671v2».SineJacobi.binomialRatio_lower` uses this bound to establish the stated
quantitative bound `1/(2*Real.sqrt (n:ℝ)) ≤ binomialRatio n`.

Article: 2606.16671v2, Theorem E.3 via `«2606.16671v2».SineJacobi.endpoint_global_bound`.

Source: mathlib, Mathlib.Analysis.SpecialFunctions.Trigonometric.Wallis — Wallis
central-binomial asymptotics.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem binomialRatio_pos (n : ℕ) : 0 < binomialRatio n := by
  induction n with
  | zero => norm_num [binomialRatio]
  | succ n ih => rw [binomialRatio]; positivity

/--
Exact identity `binomialRatio n = (Nat.centralBinom n:ℝ)/(4:ℝ)^n`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2606.16671v2, Theorem E.3.

Source: mathlib, Mathlib.Analysis.SpecialFunctions.Trigonometric.Wallis — Wallis
central-binomial asymptotics.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion. Clear the
denominators using the available nonzero hypotheses, then verify the remaining algebraic
identity.
-/
theorem binomialRatio_eq_central (n : ℕ) :
    binomialRatio n = (Nat.centralBinom n:ℝ)/(4:ℝ)^n := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  induction n with
  | zero => simp
  | succ n ih =>
    have hr := Nat.succ_mul_centralBinom_succ n
    have hc : ((n:ℝ)+1)*(Nat.centralBinom (n+1):ℝ) =
        2*(2*(n:ℝ)+1)*(Nat.centralBinom n:ℝ) := by exact_mod_cast hr
    rw [binomialRatio, ih, pow_succ]
    field_simp
    nlinarith [hc]

/--
The stated quantitative bound `binomialRatio n^2*((n:ℝ)+1) ≤ 1`.

Use: `«2606.16671v2».SineJacobi.binomialRatio_upper` uses this bound to establish the stated
quantitative bound `binomialRatio n ≤ 1/Real.sqrt ((n:ℝ)+1)`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Source: mathlib, Mathlib.Analysis.SpecialFunctions.Trigonometric.Wallis — Wallis
central-binomial asymptotics.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem binomialRatio_sq_upper (n : ℕ) : binomialRatio n^2*((n:ℝ)+1) ≤ 1 := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
    have hr : (((n:ℝ)+1/2)/((n:ℝ)+1))^2*((n:ℝ)+2) ≤ (n:ℝ)+1 := by
      rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    have hb := mul_le_mul_of_nonneg_left hr (sq_nonneg (binomialRatio n))
    calc
      _ = binomialRatio n^2*((((n:ℝ)+1/2)/((n:ℝ)+1))^2*((n:ℝ)+2)) := by
        rw [binomialRatio]
        push_cast
        ring
      _ ≤ binomialRatio n^2*((n:ℝ)+1) := hb
      _ ≤ 1 := ih

/--
The stated quantitative bound `1 ≤ 4*((n:ℝ)+1)*binomialRatio (n+1)^2`.

Use: `«2606.16671v2».SineJacobi.binomialRatio_lower` uses this bound to establish the stated
quantitative bound `1/(2*Real.sqrt (n:ℝ)) ≤ binomialRatio n`.

Article: 2606.16671v2, Theorem E.3 via `«2606.16671v2».SineJacobi.endpoint_global_bound`.

Source: mathlib, Mathlib.Analysis.SpecialFunctions.Trigonometric.Wallis — Wallis
central-binomial asymptotics.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem binomialRatio_sq_lower_succ (n : ℕ) :
    1 ≤ 4*((n:ℝ)+1)*binomialRatio (n+1)^2 := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  induction n with
  | zero => norm_num [binomialRatio]
  | succ n ih =>
    have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
    have hr : (n:ℝ)+1 ≤ (((n:ℝ)+1+1/2)/((n:ℝ)+2))^2*((n:ℝ)+2) := by
      rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith
    have hb := mul_le_mul_of_nonneg_left hr (show 0 ≤ 4*binomialRatio (n+1)^2 by positivity)
    calc
      1 ≤ 4*((n:ℝ)+1)*binomialRatio (n+1)^2 := ih
      _ ≤ 4*binomialRatio (n+1)^2*
          (((((n:ℝ)+1+1/2)/((n:ℝ)+2))^2)*((n:ℝ)+2)) := by
        convert hb using 1 ; ring
      _ = _ := by
        conv_rhs => rw [binomialRatio]
        push_cast
        ring

/--
The stated quantitative bound `binomialRatio n ≤ 1/Real.sqrt ((n:ℝ)+1)`.

Use: `«2606.16671v2».SineJacobi.ratio_bulk_bound` uses this bound to establish the stated
quantitative bound `ratio N k ≤ (1/sinc (Real.pi*b))/sqrt ((k:ℝ)+1)`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Source: mathlib, Mathlib.Analysis.SpecialFunctions.Trigonometric.Wallis — Wallis
central-binomial asymptotics.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.binomialRatio_sq_upper`,
`«2606.16671v2».SineJacobi.binomialRatio_pos` with the arguments shown in the proof.
-/
theorem binomialRatio_upper (n : ℕ) :
    binomialRatio n ≤ 1/Real.sqrt ((n:ℝ)+1) := by
  have hb := binomialRatio_sq_upper n
  have hs := Real.sq_sqrt (show 0 ≤ (n:ℝ)+1 by positivity)
  apply (le_div_iff₀ (by positivity : 0 < Real.sqrt ((n:ℝ)+1))).mpr
  have hp : 0 ≤ binomialRatio n * Real.sqrt ((n:ℝ)+1) :=
    mul_nonneg (binomialRatio_pos n).le (Real.sqrt_nonneg _)
  nlinarith

/--
The stated quantitative bound `1/(2*Real.sqrt (n:ℝ)) ≤ binomialRatio n`.

Use: `«2606.16671v2».SineJacobi.endpoint_half_bound` uses this bound to establish the stated
quantitative bound `endpoint N s ≤ (Real.pi^2/2)*Real.sqrt ((s:ℝ)+1)`.

Article: 2606.16671v2, Theorem E.3 via `«2606.16671v2».SineJacobi.endpoint_global_bound`.

Source: mathlib, Mathlib.Analysis.SpecialFunctions.Trigonometric.Wallis — Wallis
central-binomial asymptotics.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.binomialRatio_sq_lower_succ`,
`«2606.16671v2».SineJacobi.binomialRatio_pos` with the arguments shown in the proof.
-/
theorem binomialRatio_lower (n : ℕ) (hn : 0 < n) :
    1/(2*Real.sqrt (n:ℝ)) ≤ binomialRatio n := by
  -- Use the identities/estimates `«2606.16671v2».SineJacobi.binomialRatio_sq_lower_succ`,
  -- `«2606.16671v2».SineJacobi.binomialRatio_pos` with the arguments shown in the proof.
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hb := binomialRatio_sq_lower_succ k
  have hs := Real.sq_sqrt (show 0 ≤ ((k+1:ℕ):ℝ) by positivity)
  apply (div_le_iff₀ (by positivity : 0 < 2*Real.sqrt ((k+1:ℕ):ℝ))).mpr
  have hp : 0 ≤ binomialRatio (k+1) * (2*Real.sqrt ((k+1:ℕ):ℝ)) :=
    mul_nonneg (binomialRatio_pos _).le (by positivity)
  push_cast at *
  nlinarith

/--
Wallis supplies the asymptotic normalization directly, without a new Stirling proof.

Exact identity `Wallis.W n * binomialRatio n ^ 2 * (2*(n:ℝ)+1) = 1`.

Use: `«2606.16671v2».SineJacobi.binomialRatio_scaled_sq_limit` uses this identity to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun n : ℕ =>
binomialRatio n ^ 2 * (Real.pi*(n:ℝ))) atTop (𝓝 1)`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Source: mathlib, Mathlib.Analysis.SpecialFunctions.Trigonometric.Wallis — Wallis
central-binomial asymptotics.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion. Clear the
denominators using the available nonzero hypotheses, then verify the remaining algebraic
identity.
-/
theorem wallis_binomialRatio (n : ℕ) :
    Wallis.W n * binomialRatio n ^ 2 * (2*(n:ℝ)+1) = 1 := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  induction n with
  | zero => simp [Wallis.W]
  | succ n ih =>
    rw [Wallis.W_succ, binomialRatio]
    push_cast
    field_simp
    nlinarith [ih]

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun n : ℕ =>
binomialRatio n ^ 2 * (Real.pi*(n:ℝ))) atTop (𝓝 1)`.

Use: `«2606.16671v2».SineJacobi.binomialRatio_scaled_limit` uses this limit to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun n : ℕ =>
binomialRatio n * Real.sqrt (Real.pi*(n:ℝ))) atTop (𝓝 1)`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Source: mathlib, Mathlib.Analysis.SpecialFunctions.Trigonometric.Wallis — Wallis
central-binomial asymptotics.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem binomialRatio_scaled_sq_limit :
    Tendsto (fun n : ℕ => binomialRatio n ^ 2 * (Real.pi*(n:ℝ))) atTop (𝓝 1) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hb := ((tendsto_const_nhds (x := Real.pi)).mul
    Stirling.tendsto_self_div_two_mul_self_add_one).div Wallis.tendsto_W_nhds_pi_div_two
      (by positivity : Real.pi/2 ≠ 0)
  have hl : Real.pi*(1/2)/(Real.pi/2) = 1 := by field_simp
  rw [hl] at hb
  apply hb.congr'
  apply Filter.Eventually.of_forall
  intro n
  have hw := wallis_binomialRatio n
  have hwp := Wallis.W_pos n
  change Real.pi*((n:ℝ)/(2*(n:ℝ)+1))/Wallis.W n = _
  field_simp
  linear_combination -(n:ℝ)*hw

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun n : ℕ =>
binomialRatio n * Real.sqrt (Real.pi*(n:ℝ))) atTop (𝓝 1)`.

Use: `«2606.16671v2».SineJacobi.ratio_scaled_limit` uses this limit to establish convergence
along the specified source filter to the specified limit: `Tendsto (fun a => sqrt (N a:ℝ)*ratio
(N a) (k a)) l (𝓝 (1/sqrt (sin (Real.pi*t))))`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Source: mathlib, Mathlib.Analysis.SpecialFunctions.Trigonometric.Wallis — Wallis
central-binomial asymptotics.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem binomialRatio_scaled_limit :
    Tendsto (fun n : ℕ => binomialRatio n * Real.sqrt (Real.pi*(n:ℝ))) atTop (𝓝 1) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have hb := Real.continuous_sqrt.continuousAt.tendsto.comp binomialRatio_scaled_sq_limit
  simp only [Real.sqrt_one] at hb
  convert hb using 1
  funext n
  change binomialRatio n * Real.sqrt (Real.pi*(n:ℝ)) =
    Real.sqrt (binomialRatio n^2*(Real.pi*(n:ℝ)))
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (binomialRatio_pos n).le]

end
end «2606.16671v2».SineJacobi
