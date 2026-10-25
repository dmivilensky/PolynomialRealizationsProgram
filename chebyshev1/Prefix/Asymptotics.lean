import chebyshev1.Prefix.Gain
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Article: chebyshev1, Theorem 2.2.
The asymptotic statement also uses mathlib's standard equivalence relation.
Use: `chebyshev1.Prefix.gain_isEquivalent_rpow` feeds
`chebyshev1.TwoTerm.optimal_asymptotic` (The asymptotic optimal value for any family of finite
prefix-exact recurrences).
-/
namespace chebyshev1.Prefix
noncomputable section
open Filter
open scoped Topology Asymptotics
variable (I : SpectralInterval)

/--
The stated quantitative bound `0 ≤ shape N`.

Use: `chebyshev1.Prefix.normalized_gain_eq` rewrites with this bound to establish exact
identity `(realization I).gain I N * I.delta / (I.epsilon N * (N : ℝ) * Real.sqrt N) = 2 *
Real.sqrt ((4 / 3 : ℝ) - 1 / N + (2 / 3 : ℝ) * (1 / N) ^ 2)`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.gain_eventually_lt_prefix`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem shape_nonneg (N : ℕ) (hN : 1 ≤ N) : 0 ≤ shape N := by
  dsimp [shape]
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : (0 : ℝ) ≤ N - 1 := by linarith
  have h2 : (0 : ℝ) ≤ 2 * N - 1 := by linarith
  positivity

/--
Exact identity `(realization I).gain I N * I.delta / (I.epsilon N * (N : ℝ) * Real.sqrt N) = 2
* Real.sqrt ((4 / 3 : ℝ) - 1 / N + (2 / 3 : ℝ) * (1 / N) ^ 2)`.

Use: `chebyshev1.Prefix.gain_asymptotic` uses this identity to establish convergence along
the specified source filter to the specified limit: `Tendsto (fun N : ℕ => (realization I).gain
I N * I.delta / (I.epsilon N * (N : ℝ) * Real.sqrt N)) atTop (𝓝 (4 / Real.sqrt 3))`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.gain_eventually_lt_prefix`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem normalized_gain_eq (N : ℕ) (hN : 1 ≤ N) :
    (realization I).gain I N * I.delta /
      (I.epsilon N * (N : ℝ) * Real.sqrt N) =
      2 * Real.sqrt ((4 / 3 : ℝ) - 1 / N + (2 / 3 : ℝ) * (1 / N) ^ 2) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hs := Real.sqrt_pos.mpr hn
  have he : I.epsilon N ≠ 0 := by dsimp [SpectralInterval.epsilon]; exact one_div_ne_zero (I.den_ne N)
  have hd : I.delta ≠ 0 := ne_of_gt I.delta_pos
  have hpoly : shape N / ((N : ℝ) * Real.sqrt N) ^ 2 =
      (4 / 3 : ℝ) - 1 / N + (2 / 3 : ℝ) * (1 / N) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hn.le]
    dsimp [shape]
    field_simp
    ring
  rw [← hpoly, Real.sqrt_div (shape_nonneg N hN),
    Real.sqrt_sq_eq_abs, abs_of_pos (mul_pos hn hs), gain_exact I N hN]
  field_simp

/--
The asymptotic assertion of Theorem 2.2; `N * sqrt N` is `N^(3/2)`.

Convergence along the specified source filter to the specified limit: `Tendsto (fun N : ℕ =>
(realization I).gain I N * I.delta / (I.epsilon N * (N : ℝ) * Real.sqrt N)) atTop (𝓝 (4 /
Real.sqrt 3))`.

Use: `chebyshev1.Prefix.gain_asymptotic_ratio` uses this limit to establish convergence
along the specified source filter to the specified limit: `Tendsto (fun N : ℕ => (realization
I).gain I N / leadingGain I N) atTop (𝓝 1)`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.gain_eventually_lt_prefix`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem gain_asymptotic :
    Tendsto (fun N : ℕ => (realization I).gain I N * I.delta /
      (I.epsilon N * (N : ℝ) * Real.sqrt N)) atTop (𝓝 (4 / Real.sqrt 3)) := by
  -- Record the convergence h with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have h : Tendsto (fun N : ℕ => (4 / 3 : ℝ) - 1 / N +
      (2 / 3 : ℝ) * (1 / N) ^ 2) atTop (𝓝 (4 / 3 : ℝ)) := by
    -- Record the convergence hi with its source filter and target limit before taking limits
    -- in the subsequent identities/bounds.
    have hi : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    convert! (tendsto_const_nhds.sub hi).add (hi.pow 2 |>.const_mul (2 / 3 : ℝ)) using 1
    norm_num
  have hc : 2 * Real.sqrt (4 / 3 : ℝ) = 4 / Real.sqrt 3 := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
    ring
  rw [← hc]
  apply (h.sqrt.const_mul 2).congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  exact (normalized_gain_eq I N hN).symm

/--
Defines `leadingGain` of type `ℝ` by `(4 / Real.sqrt 3) * (N : ℝ) * Real.sqrt N * I.epsilon N /
I.delta`.

Use: `chebyshev1.Prefix.gain_asymptotic_ratio` rewrites with this definition to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun N : ℕ =>
(realization I).gain I N / leadingGain I N) atTop (𝓝 1)`.

Article: chebyshev1, Theorem 2.2 via `chebyshev1.Prefix.gain_isEquivalent_rpow`.
-/
def leadingGain (N : ℕ) : ℝ :=
  (4 / Real.sqrt 3) * (N : ℝ) * Real.sqrt N * I.epsilon N / I.delta

/--
Exact identity `leadingGain I N = (4 / Real.sqrt 3) * (N : ℝ) ^ (3 / 2 : ℝ) * I.epsilon N /
I.delta`.

Use: `chebyshev1.Prefix.gain_isEquivalent_rpow` uses this identity to establish the stated
quantitative bound `(fun N : ℕ => (realization I).gain I N) ~[atTop] (fun N : ℕ => (4 /
Real.sqrt 3) * (N : ℝ) ^ (3 / 2 : ℝ) * I.epsilon N / I.delta)`.

Article: chebyshev1, Theorem 2.2 via `chebyshev1.Prefix.gain_isEquivalent_rpow`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem leadingGain_rpow (N : ℕ) :
    leadingGain I N = (4 / Real.sqrt 3) * (N : ℝ) ^ (3 / 2 : ℝ) * I.epsilon N / I.delta := by
  have hp : (N : ℝ) ^ (3 / 2 : ℝ) = (N : ℝ) * Real.sqrt N := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add' (by positivity) (by norm_num), Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hp]
  dsimp [leadingGain]
  ring

/--
Relative error tends to zero, as required by the `1 + o(1)` in the paper.

Convergence along the specified source filter to the specified limit: `Tendsto (fun N : ℕ =>
(realization I).gain I N / leadingGain I N) atTop (𝓝 1)`.

Use: `chebyshev1.Prefix.gain_isEquivalent` uses this limit to establish the stated
quantitative bound `(fun N : ℕ => (realization I).gain I N) ~[atTop] leadingGain I`.

Article: chebyshev1, Theorem 2.2 via `chebyshev1.Prefix.gain_isEquivalent_rpow`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem gain_asymptotic_ratio :
    Tendsto (fun N : ℕ => (realization I).gain I N / leadingGain I N) atTop (𝓝 1) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have hc : (4 / Real.sqrt 3 : ℝ) ≠ 0 := by positivity
  have h := (gain_asymptotic I).div_const (4 / Real.sqrt 3)
  rw [div_self hc] at h
  convert! h using 1
  funext N
  simp only [leadingGain, div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

/--
The asymptotic statement also uses mathlib's standard equivalence relation.

The stated quantitative bound `(fun N : ℕ => (realization I).gain I N) ~[atTop] leadingGain I`.

Use: `chebyshev1.Prefix.gain_isEquivalent_rpow` uses this identity to establish the stated
quantitative bound `(fun N : ℕ => (realization I).gain I N) ~[atTop] (fun N : ℕ => (4 /
Real.sqrt 3) * (N : ℝ) ^ (3 / 2 : ℝ) * I.epsilon N / I.delta)`.

Article: chebyshev1, Theorem 2.2 via `chebyshev1.Prefix.gain_isEquivalent_rpow`.

Proof: Use the identities/estimates `chebyshev1.Prefix.gain_asymptotic_ratio` with the
arguments shown in the proof.
-/
theorem gain_isEquivalent :
    (fun N : ℕ => (realization I).gain I N) ~[atTop] leadingGain I :=
  Asymptotics.isEquivalent_of_tendsto_one (gain_asymptotic_ratio I)

/--
The stated quantitative bound `(fun N : ℕ => (realization I).gain I N) ~[atTop] (fun N : ℕ =>
(4 / Real.sqrt 3) * (N : ℝ) ^ (3 / 2 : ℝ) * I.epsilon N / I.delta)`.

Use: `chebyshev1.TwoTerm.optimal_asymptotic` uses this identity to establish the stated
quantitative bound `(fun N : ℕ => (S N).realization.gain I N) ~[Filter.atTop] (fun N : ℕ => (4
/ Real.sqrt 3) * (N : ℝ) ^ (3 / 2 : ℝ) * I.epsilon N / I.delta)`.

Article: chebyshev1, Theorem 2.2.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem gain_isEquivalent_rpow :
    (fun N : ℕ => (realization I).gain I N) ~[atTop]
      (fun N : ℕ => (4 / Real.sqrt 3) * (N : ℝ) ^ (3 / 2 : ℝ) * I.epsilon N / I.delta) := by
  have heq : leadingGain I =
      (fun N : ℕ => (4 / Real.sqrt 3) * (N : ℝ) ^ (3 / 2 : ℝ) * I.epsilon N / I.delta) :=
    funext (leadingGain_rpow I)
  rw [← heq]
  exact gain_isEquivalent I

end
end chebyshev1.Prefix
