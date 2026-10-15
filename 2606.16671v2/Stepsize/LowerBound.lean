import «2606.16671v2».Stepsize.Basic
import «2606.16671v2».Chebyshev.EndpointDerivatives
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Article: 2606.16671v2, Theorem 1.4.
The `O(N^-2)` remainder in the asymptotic bound of Theorem 1.4.
Result: `«2606.16671v2».Stepsize.lowerBound_asymptotic` supplies the stated article conclusion.
-/
namespace «2606.16671v2».Stepsize
noncomputable section
open Filter
open scoped BigOperators Topology Asymptotics

/--
Defines `lowerBound` of type `ℝ` by `2 * I.epsilon N / I.delta * Real.sqrt (((2 : ℝ) * N ^ 4 +
N ^ 2) / 3)`.

Use: `«2606.16671v2».Stepsize.lowerBound_asymptotic` uses this definition to establish the
precise assertion is `lowerBound I ~[atTop] leadingBound I`.

Article: 2606.16671v2, Theorem 1.4 via `«2606.16671v2».Stepsize.gain_lower_bound`.
-/
def lowerBound (I : SpectralInterval) (N : ℕ) : ℝ :=
  2 * I.epsilon N / I.delta * Real.sqrt (((2 : ℝ) * N ^ 4 + N ^ 2) / 3)

/--
The endpoint energy is independent of the ordering of an exact schedule.

Exact identity `(∑ s ∈ Finset.range N, ((realization gamma).kernel N s I.mu I.mu) ^ 2) = (2 *
I.epsilon N / I.delta) ^ 2 * (((2 : ℝ) * N ^ 4 + N ^ 2) / 3)`.

Use: `«2606.16671v2».Stepsize.endpoint_kernelNorm` rewrites with this identity to establish
exact identity `(realization gamma).kernelNorm N I.mu I.mu = lowerBound I N`.

Article: 2606.16671v2, Theorem 1.4.

Proof: Use the identities/estimates `«2606.16671v2».Stepsize.kernel_square_sum_derivatives`,
`«2606.16671v2».Stepsize.final_polynomial_eq`,
`«2606.16671v2».SpectralInterval.residual_eval_mu` with the arguments shown in the proof.
-/
theorem endpoint_square_sum (gamma : ℕ → ℝ) (I : SpectralInterval) (N : ℕ)
    (h : FinalExact gamma I N) :
    (∑ s ∈ Finset.range N, ((realization gamma).kernel N s I.mu I.mu) ^ 2) =
      (2 * I.epsilon N / I.delta) ^ 2 * (((2 : ℝ) * N ^ 4 + N ^ 2) / 3) := by
  rw [kernel_square_sum_derivatives, final_polynomial_eq gamma I N h,
    I.residual_eval_mu, I.residual_derivative_eval_mu, I.residual_second_derivative_eval_mu]
  ring

/--
Exact identity `(realization gamma).kernelNorm N I.mu I.mu = lowerBound I N`.

Use: `«2606.16671v2».Stepsize.gain_lower_bound` rewrites with this identity to establish the
stated quantitative bound `lowerBound I N ≤ (realization gamma).gain I N`.

Article: 2606.16671v2, Theorem 1.4 via `«2606.16671v2».Stepsize.gain_lower_bound`.

Proof: Use the identities/estimates `«2606.16671v2».Stepsize.endpoint_square_sum`,
`«2606.16671v2».SpectralInterval.den_pos`, `«2606.16671v2».SpectralInterval.delta_pos` with the
arguments shown in the proof.
-/
theorem endpoint_kernelNorm (gamma : ℕ → ℝ) (I : SpectralInterval) (N : ℕ)
    (h : FinalExact gamma I N) :
    (realization gamma).kernelNorm N I.mu I.mu = lowerBound I N := by
  -- Use the identities/estimates `«2606.16671v2».Stepsize.endpoint_square_sum`,
  -- `«2606.16671v2».SpectralInterval.den_pos`, `«2606.16671v2».SpectralInterval.delta_pos`
  -- with the arguments shown in the proof.
  rw [Realization.kernelNorm, endpoint_square_sum gamma I N h,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  have hc : 0 < 2 * I.epsilon N / I.delta :=
    div_pos (mul_pos (by norm_num) (one_div_pos.mpr (I.den_pos N))) I.delta_pos
  rw [abs_of_pos hc]
  rfl

/--
Theorem 1.4. Positivity of individual stepsizes is not needed for this bound.

The stated quantitative bound `lowerBound I N ≤ (realization gamma).gain I N`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2606.16671v2, Theorem 1.4.

Proof: Use the identities/estimates `«2606.16671v2».Stepsize.endpoint_kernelNorm`,
`«2606.16671v2».Realization.kernelNorm_le_gain` with the arguments shown in the proof.
-/
theorem gain_lower_bound (gamma : ℕ → ℝ) (I : SpectralInterval) (N : ℕ) (_hN : 1 ≤ N)
    (h : FinalExact gamma I N) : lowerBound I N ≤ (realization gamma).gain I N := by
  rw [← endpoint_kernelNorm gamma I N h]
  exact Realization.kernelNorm_le_gain _ I N ⟨le_rfl, I.mu_lt_L.le⟩ ⟨le_rfl, I.mu_lt_L.le⟩

/--
Defines `correction` of type `ℝ` by `Real.sqrt (1 + 1 / (2 * (N : ℝ) ^ 2))`.

Use: `«2606.16671v2».Stepsize.correction_error_bound` uses this definition to establish the
stated quantitative bound `|correction N - 1| ≤ (1 / 2 : ℝ) * |1 / (N : ℝ) ^ 2|`.

Article: 2606.16671v2, Theorem 1.4 via `«2606.16671v2».Stepsize.correction_error_isBigO`.
-/
def correction (N : ℕ) : ℝ := Real.sqrt (1 + 1 / (2 * (N : ℝ) ^ 2))
/--
Defines `leadingBound` of type `ℝ` by `2 * Real.sqrt (2 / 3 : ℝ) * (N : ℝ) ^ 2 * I.epsilon N /
I.delta`.

Use: `«2606.16671v2».Stepsize.lowerBound_asymptotic` uses this definition to establish the
precise assertion is `lowerBound I ~[atTop] leadingBound I`.

Article: 2606.16671v2, Theorem 1.4 via `«2606.16671v2».Stepsize.lowerBound_asymptotic`.
-/
def leadingBound (I : SpectralInterval) (N : ℕ) : ℝ :=
  2 * Real.sqrt (2 / 3 : ℝ) * (N : ℝ) ^ 2 * I.epsilon N / I.delta

/--
Exact identity `lowerBound I N = leadingBound I N * correction N`.

Use: `«2606.16671v2».Stepsize.lowerBound_asymptotic` rewrites with this identity to establish
the precise assertion is `lowerBound I ~[atTop] leadingBound I`.

Article: 2606.16671v2, Theorem 1.4 via `«2606.16671v2».Stepsize.lowerBound_asymptotic`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem lowerBound_factorization (I : SpectralInterval) (N : ℕ) (hN : 1 ≤ N) :
    lowerBound I N = leadingBound I N * correction N := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hpoly : ((2 : ℝ) * N ^ 4 + N ^ 2) / 3 =
      (2 / 3 : ℝ) * ((N : ℝ) ^ 2) ^ 2 * (1 + 1 / (2 * (N : ℝ) ^ 2)) := by
    field_simp
  dsimp [lowerBound, leadingBound, correction]
  rw [hpoly, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 / 3 : ℝ) * ((N : ℝ) ^ 2) ^ 2),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 / 3), Real.sqrt_sq (sq_nonneg _)]
  ring

/--
The stated quantitative bound `|correction N - 1| ≤ (1 / 2 : ℝ) * |1 / (N : ℝ) ^ 2|`.

Use: `«2606.16671v2».Stepsize.correction_error_isBigO` uses this bound to establish the stated
quantitative bound `(fun N : ℕ => correction N - 1) =O[atTop] (fun N : ℕ => 1 / (N : ℝ) ^ 2)`.

Article: 2606.16671v2, Theorem 1.4 via `«2606.16671v2».Stepsize.correction_error_isBigO`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem correction_error_bound (N : ℕ) :
    |correction N - 1| ≤ (1 / 2 : ℝ) * |1 / (N : ℝ) ^ 2| := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  have hx : (0 : ℝ) ≤ 1 / (2 * (N : ℝ) ^ 2) := by positivity
  have hs := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 1 + 1 / (2 * (N : ℝ) ^ 2))
  have hc : 1 ≤ correction N := by
    dsimp [correction]
    exact (Real.le_sqrt (by norm_num) (by linarith)).mpr (by nlinarith)
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by positivity)]
  dsimp [correction] at hc ⊢
  have he : 1 / (2 * (N : ℝ) ^ 2) = (1 / 2 : ℝ) * (1 / (N : ℝ) ^ 2) := by ring
  rw [← he]
  nlinarith

/--
The `O(N^-2)` remainder in the asymptotic bound of Theorem 1.4.

The stated quantitative bound `(fun N : ℕ => correction N - 1) =O[atTop] (fun N : ℕ => 1 / (N :
ℝ) ^ 2)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2606.16671v2, Theorem 1.4.

Proof: Use the identities/estimates `«2606.16671v2».Stepsize.correction_error_bound` with the
arguments shown in the proof.
-/
theorem correction_error_isBigO :
    (fun N : ℕ => correction N - 1) =O[atTop] (fun N : ℕ => 1 / (N : ℝ) ^ 2) := by
  apply Asymptotics.IsBigO.of_bound (1 / 2 : ℝ)
  exact Filter.Eventually.of_forall (fun N => by simpa only [Real.norm_eq_abs] using correction_error_bound N)

/--
Convergence along the specified source filter to the specified limit: `Tendsto correction atTop
(𝓝 1)`.

Use: `«2606.16671v2».Stepsize.lowerBound_asymptotic` uses this limit to establish the precise
assertion is `lowerBound I ~[atTop] leadingBound I`.

Article: 2606.16671v2, Theorem 1.4 via `«2606.16671v2».Stepsize.lowerBound_asymptotic`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem correction_tendsto : Tendsto correction atTop (𝓝 1) := by
  -- Record the convergence hi with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hi : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have h := (tendsto_const_nhds (x := (1 : ℝ))).add ((hi.pow 2).const_mul (1 / 2 : ℝ))
  convert! h.sqrt using 1
  · funext N
    dsimp [correction]
    congr 1
    ring
  · norm_num

/--
The precise assertion is `lowerBound I ~[atTop] leadingBound I`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2606.16671v2, Theorem 1.4.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem lowerBound_asymptotic (I : SpectralInterval) :
    lowerBound I ~[atTop] leadingBound I := by
  apply Asymptotics.isEquivalent_iff_exists_eq_mul.mpr
  refine ⟨correction, correction_tendsto, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  change lowerBound I N = correction N * leadingBound I N
  rw [lowerBound_factorization I N hN, mul_comm]

end
end «2606.16671v2».Stepsize
