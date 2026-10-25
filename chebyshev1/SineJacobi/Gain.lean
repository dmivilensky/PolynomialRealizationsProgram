import chebyshev1.SineJacobi.Reversal
import chebyshev1.Jacobi.Gain
import chebyshev1.Realization.StaticShift

/-!
Article: chebyshev1, Theorem 5.2.
The exact finite gain of Theorem 5.2, in endpoint-product coordinates.
Use: `chebyshev1.SineJacobi.gain_exact` feeds `chebyshev1.SineJacobi.gain_asymptotic_ratio`
(Theorem 5.2: the ratio to the stated N^(3/2) leading term tends to one).
-/
namespace chebyshev1.SineJacobi
noncomputable section
open Polynomial Real
open scoped BigOperators
variable (I : SpectralInterval)

/--
Defines `greenWeight` of type `ℝ` by `endpoint N s*endpoint N (N-s-1)`.

Use: `chebyshev1.SineJacobi.gain_exact` uses this definition to establish the identity
`((data N).realization I).gain I N = 2*I.epsilon N/I.delta * sqrt (∑ s ∈ Finset.range N,
(greenWeight N s)^2)`.

Article: chebyshev1, Theorem 5.1 via
`chebyshev1.SineJacobi.diagonalProfile_eLpNorm_limit`.
-/
def greenWeight (N s : ℕ) : ℝ := endpoint N s*endpoint N (N-s-1)

/--
Exact identity `((data N).realization I).residualPolynomial N = I.residual N`.

Use: `chebyshev1.SineJacobi.greenWeight_sum` rewrites with this identity to establish exact
identity `∑ s ∈ Finset.range N, greenWeight N s = (N:ℝ)^2`.

Article: chebyshev1, Corollary 5.3 via `chebyshev1.SineJacobi.opNorm_linearResponse_le`.

Proof: Use the identities/estimates `chebyshev1.JacobiData.residualPolynomial_eq`,
`chebyshev1.SineJacobi.admissible`, `chebyshev1.JacobiData.terminal_residual` with the
arguments shown in the proof.
-/
theorem residualPolynomial (N : ℕ) (hN : 0 < N) :
    ((data N).realization I).residualPolynomial N = I.residual N := by
  rw [JacobiData.residualPolynomial_eq _ I (admissible I N hN) N le_rfl]
  exact (data N).terminal_residual I (by positivity) (terminal N hN)

/--
The stated quantitative bound `|((data N).realization I).kernel N s lam nu| ≤ |((data
N).realization I).kernel N s I.mu I.mu|`.

Use: `chebyshev1.SineJacobi.gain_eq_endpoint` uses this bound to establish the identity
`((data N).realization I).gain I N = ((data N).realization I).kernelNorm N I.mu I.mu`.

Article: chebyshev1, Theorem E.1.

Proof: Use the identities/estimates `chebyshev1.JacobiData.kernel_eq`,
`chebyshev1.SineJacobi.admissible`, `chebyshev1.SineJacobi.tail_eq_leading_of_end` with
the arguments shown in the proof.
-/
theorem kernel_abs_le_endpoint (N s : ℕ) (hs : s < N) {lam nu : ℝ}
    (hl : lam ∈ Set.Icc I.mu I.L) (hn : nu ∈ Set.Icc I.mu I.L) :
    |((data N).realization I).kernel N s lam nu| ≤
      |((data N).realization I).kernel N s I.mu I.mu| := by
  -- Use the identities/estimates `chebyshev1.JacobiData.kernel_eq`,
  -- `chebyshev1.SineJacobi.admissible`, `chebyshev1.SineJacobi.tail_eq_leading_of_end`
  -- with the arguments shown in the proof.
  have hN : 0 < N := by omega
  rw [JacobiData.kernel_eq _ I (admissible I N hN) s hs,
    JacobiData.kernel_eq _ I (admissible I N hN) s hs]
  rw [tail_eq_leading_of_end N (s+1) (N-(s+1)) (by omega)]
  simp only [I.z_mu, abs_mul]
  rw [abs_of_pos (leading_eval_one_pos N (N-(s+1)) (by omega)),
    abs_of_pos (leading_eval_one_pos N s hs)]
  rw [mul_assoc, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact mul_le_mul (leading_endpoint_max N (N-(s+1)) (by omega) _ (I.z_mem hl))
    (leading_endpoint_max N s hs _ (I.z_mem hn)) (abs_nonneg _)
      (leading_eval_one_pos N (N-(s+1)) (by omega)).le

/--
Exact identity `((data N).realization I).gain I N = ((data N).realization I).kernelNorm N I.mu
I.mu`.

Use: `chebyshev1.SineJacobi.gain_exact` rewrites with this identity to establish exact
identity `((data N).realization I).gain I N = 2*I.epsilon N/I.delta * sqrt (∑ s ∈ Finset.range
N, (greenWeight N s)^2)`.

Article: chebyshev1, Theorem E.1.

Proof: Use the identities/estimates `chebyshev1.Realization.gainValues_nonempty`,
`chebyshev1.SineJacobi.kernel_abs_le_endpoint`,
`chebyshev1.Realization.kernelNorm_le_gain` with the arguments shown in the proof.
-/
theorem gain_eq_endpoint (N : ℕ) (_hN : 0 < N) :
    ((data N).realization I).gain I N = ((data N).realization I).kernelNorm N I.mu I.mu := by
  -- Use the identities/estimates `chebyshev1.Realization.gainValues_nonempty`,
  -- `chebyshev1.SineJacobi.kernel_abs_le_endpoint`,
  -- `chebyshev1.Realization.kernelNorm_le_gain` with the arguments shown in the proof.
  apply le_antisymm
  · apply csSup_le (((data N).realization I).gainValues_nonempty I N)
    rintro v ⟨lam,hl,nu,hn,rfl⟩
    apply sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro s hs
    exact sq_le_sq.mpr (kernel_abs_le_endpoint I N s (Finset.mem_range.mp hs) hl hn)
  · exact ((data N).realization I).kernelNorm_le_gain I N ⟨le_rfl,I.mu_lt_L.le⟩ ⟨le_rfl,I.mu_lt_L.le⟩

/--
Exact identity `((data N).realization I).kernel N s I.mu I.mu = -(2*I.epsilon
N/I.delta)*greenWeight N s`.

Use: `chebyshev1.SineJacobi.gain_exact` rewrites with this identity to establish exact
identity `((data N).realization I).gain I N = 2*I.epsilon N/I.delta * sqrt (∑ s ∈ Finset.range
N, (greenWeight N s)^2)`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.gain_exact`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem kernel_endpoint (N s : ℕ) (hs : s < N) :
    ((data N).realization I).kernel N s I.mu I.mu =
      -(2*I.epsilon N/I.delta)*greenWeight N s := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hN : 0 < N := by omega
  rw [JacobiData.kernel_eq _ I (admissible I N hN) s hs, I.z_mu,
    tail_eq_leading_of_end N (s+1) (N-(s+1)) (by omega)]
  have hd : (data N).den I N = (2/(2:ℝ)^N)*I.den N := by
    simp [JacobiData.den, terminal N hN, SpectralInterval.den]
  have hp : (2:ℝ)^N = 2^s*2^(N-s-1)*2 := by
    rw [← pow_add, ← pow_succ]
    congr 1
    omega
  rw [hd, hp]
  unfold greenWeight endpoint SpectralInterval.epsilon
  rw [show N-(s+1) = N-s-1 by omega]
  field_simp

/--
Exact identity `∑ s ∈ Finset.range N, greenWeight N s = (N:ℝ)^2`.

Use: `chebyshev1.SineJacobi.endpoint_product_sum_limit` rewrites with this identity to
establish convergence along the specified source filter to the specified limit: `Tendsto (fun N
: ℕ => (∑ s ∈ Finset.range N, endpoint N s*endpoint N (N-s-1))/(Real.pi*(N:ℝ)^2)) atTop (𝓝
sineIntegral)`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.resolvent_trace`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem greenWeight_sum (I : SpectralInterval) (N : ℕ) (hN : 0 < N) :
    ∑ s ∈ Finset.range N, greenWeight N s = (N:ℝ)^2 := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  have hd := ((data N).realization I).kernel_sum_derivative N I.mu
  rw [residualPolynomial I N hN, I.residual_derivative_eval_mu] at hd
  have he : ∑ s ∈ Finset.range N, ((data N).realization I).kernel N s I.mu I.mu =
      -(2*I.epsilon N/I.delta)*(∑ s ∈ Finset.range N, greenWeight N s) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun s hs => kernel_endpoint I N s (Finset.mem_range.mp hs))
  rw [he] at hd
  have hc : -(2*I.epsilon N/I.delta) ≠ 0 := by
    dsimp [SpectralInterval.epsilon]
    exact neg_ne_zero.mpr (div_ne_zero (mul_ne_zero (by norm_num) (one_div_ne_zero (I.den_ne N)))
      (ne_of_gt I.delta_pos))
  apply mul_left_cancel₀ hc
  calc _ = _ := hd
       _ = _ := by ring

/--
The exact finite gain of Theorem 5.2, in endpoint-product coordinates.

Exact identity `((data N).realization I).gain I N = 2*I.epsilon N/I.delta * sqrt (∑ s ∈
Finset.range N, (greenWeight N s)^2)`.

Use: `chebyshev1.SineJacobi.gain_asymptotic_ratio` rewrites with this identity to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun N : ℕ =>
((data N).realization I).gain I N/ ((2*sqrt sineEnergy/I.delta)*(N:ℝ)^(3/2:ℝ)*I.epsilon N))
atTop (𝓝 1)`.

Article: chebyshev1, Theorem 5.2.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem gain_exact (N : ℕ) (hN : 0 < N) :
    ((data N).realization I).gain I N =
      2*I.epsilon N/I.delta * sqrt (∑ s ∈ Finset.range N, (greenWeight N s)^2) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  rw [gain_eq_endpoint I N hN, Realization.kernelNorm]
  have he : (∑ s ∈ Finset.range N, (((data N).realization I).kernel N s I.mu I.mu)^2) =
      (2*I.epsilon N/I.delta)^2*(∑ s ∈ Finset.range N, (greenWeight N s)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [kernel_endpoint I N s (Finset.mem_range.mp hs)]
    ring
  rw [he, sqrt_mul (sq_nonneg _), sqrt_sq_eq_abs]
  have heps : 0 < I.epsilon N := one_div_pos.mpr (I.den_pos N)
  rw [abs_of_pos (div_pos (mul_pos (by norm_num) heps) I.delta_pos)]

end
end chebyshev1.SineJacobi
