import «2610.05164v2».Finite.Subclasses
import «2610.05164v2».Green.Positivity
import «2606.16671v2».Jacobi.Gain
import «2606.16671v2».Jacobi.Resolvent
import «2606.16671v2».Spectral.Sharpness
import «2606.16671v2».Chebyshev.EndpointDerivatives
import «2606.16671v2».Realization.StaticShift

/-!
Article: 2610.05164v2, Theorem A.1.
Lemma 1: the trace is fixed throughout the complete Jacobi fiber.
Use: `«2610.05164v2».Jacobi.green_trace` feeds
`«2610.05164v2».Packing.Representation.atomic_matrix_traceBound` (atomic matrix trace Bound).
-/
namespace «2610.05164v2».Jacobi
noncomputable section
open «2606.16671v2» Polynomial Polynomial.Chebyshev
open scoped BigOperators
variable {N : ℕ} (J : Jacobi N) (I : SpectralInterval)

/--
Defines `gain` of type `ℝ` by `(J.recurrence I h).method.realization.gain I N`.

Use: `«2610.05164v2».Jacobi.gain_attained_dim_two` uses this definition to establish the
identity stated in that declaration.

Article: 2610.05164v2, Corollary 1 via `«2610.05164v2».Jacobi.symmetric_gain_bounds`.
-/
def gain (h : J.data.Admissible I N) : ℝ := (J.recurrence I h).method.realization.gain I N

/--
Exact identity `J.gain I h = (J.data.realization I).gain I N`.

Use: `«2610.05164v2».Jacobi.gain_formula` rewrites with this identity to establish exact
identity `J.gain I h = 2/(I.delta*J.data.den I N)*sSup (J.data.blockGainValues N)`.

Article: 2610.05164v2, Theorem 1.2 via
`«2610.05164v2».DualCertificate.uniform_sine_of_finite_lower`.

Proof: Use the identities/estimates `«2610.05164v2».Horizon.gain_eq`,
`«2610.05164v2».Jacobi.recurrence_agree` with the arguments shown in the proof.
-/
theorem gain_eq (h : J.data.Admissible I N) :
    J.gain I h = (J.data.realization I).gain I N :=
  Horizon.gain_eq (J.recurrence_agree I h) I

/--
The exact maximizing polynomial expression in Theorem 2.2.

Exact identity `J.gain I h = 2/(I.delta*J.data.den I N)*sSup (J.data.blockGainValues N)`.

Use: `«2610.05164v2».Jacobi.normalized_gain` rewrites with this identity to establish exact
identity `I.delta*J.gain I (J.admissible I hN ht) / ((N:ℝ)^(3/2:ℝ)*I.epsilon N) =
2/((N:ℝ)^(3/2:ℝ)*(J.data.leading N).eval 1)*sSup (J.data.blockGainValues N)`.

Article: 2610.05164v2, Theorem 2.2.

Proof: Use the identities/estimates `«2610.05164v2».Jacobi.gain_eq`,
`«2606.16671v2».JacobiData.gain_eq_blocks` with the arguments shown in the proof.
-/
theorem gain_formula (h : J.data.Admissible I N) :
    J.gain I h = 2/(I.delta*J.data.den I N)*sSup (J.data.blockGainValues N) := by rw [J.gain_eq I h, J.data.gain_eq_blocks I h, abs_of_pos (h N le_rfl)]

/--
Exact identity `J.green s s = (J.data.leading s.val).eval 1 * (J.data.block (s.val+1)
(N-(s.val+1))).eval 1 / (J.data.leading N).eval 1`.

Use: `«2610.05164v2».Jacobi.kernel_endpoint` rewrites with this identity to establish exact
identity `(J.data.realization I).kernel N s.val I.mu I.mu = -(2*I.epsilon N/I.delta)*J.green s
s`.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».Jacobi.green_trace`.

Proof: Use the identities/estimates `«2606.16671v2».JacobiData.resolvent_diagonal` with the
arguments shown in the proof.
-/
theorem green_diagonal (hN : 0 < N) (s : Fin N) :
    J.green s s = (J.data.leading s.val).eval 1 *
      (J.data.block (s.val+1) (N-(s.val+1))).eval 1 / (J.data.leading N).eval 1 := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  have he := J.data.resolvent_diagonal n s 1 J.coupling_nonneg
  simpa only [show Matrix.scalar (Fin (n+1)) (1:ℝ) = 1 by simp [Matrix.scalar],
    show n.succ-(s.val+1) = n-s.val by omega,
    green, matrix, Nat.succ_eq_add_one] using he

/--
The stated quantitative bound `0 < (J.data.leading N).eval 1`.

Use: `«2610.05164v2».Jacobi.kernel_endpoint` uses this bound to establish the identity
`(J.data.realization I).kernel N s.val I.mu I.mu = -(2*I.epsilon N/I.delta)*J.green s s`.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».Jacobi.green_trace`.

Proof: Use the identities/estimates `«2610.05164v2».fiberPolynomial_eq` with the arguments
shown in the proof.
-/
theorem leading_endpoint_pos (hN : 0 < N) (ht : J.Terminal) :
    0 < (J.data.leading N).eval 1 := by
  rw [ht, fiberPolynomial_eq N hN]
  simp only [eval_mul, eval_C, T_eval_one, mul_one]
  positivity

/--
Exact identity `(J.data.leading N).eval 1 / J.data.den I N = I.epsilon N`.

Use: `«2610.05164v2».Jacobi.kernel_endpoint` uses this identity to establish the identity
`(J.data.realization I).kernel N s.val I.mu I.mu = -(2*I.epsilon N/I.delta)*J.green s s`.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».Jacobi.green_trace`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem endpoint_ratio (hN : 0 < N) (ht : J.Terminal) :
    (J.data.leading N).eval 1 / J.data.den I N = I.epsilon N := by
  rw [JacobiData.den, ht, fiberPolynomial_eq N hN]
  simp only [eval_mul, eval_C, T_eval_one, mul_one]
  change 2/(2:ℝ)^N / (2/(2:ℝ)^N * I.den N) = 1/I.den N
  field_simp [I.den_ne N]

/--
At the spectral endpoint the response kernel is the actual Green diagonal.

Exact identity `(J.data.realization I).kernel N s.val I.mu I.mu = -(2*I.epsilon
N/I.delta)*J.green s s`.

Use: `«2610.05164v2».Jacobi.endpoint_norm` uses this identity to establish the identity
`(J.data.realization I).kernelNorm N I.mu I.mu = 2*I.epsilon N/I.delta*Real.sqrt J.energy`.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».Jacobi.green_trace`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem kernel_endpoint (hN : 0 < N) (ht : J.Terminal) (s : Fin N) :
    (J.data.realization I).kernel N s.val I.mu I.mu =
      -(2*I.epsilon N/I.delta)*J.green s s := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have h := J.admissible I hN ht
  rw [J.data.kernel_eq I h s.val s.isLt, I.z_mu, J.green_diagonal hN s]
  have hr := J.endpoint_ratio I hN ht
  field_simp [(J.leading_endpoint_pos hN ht).ne', (h N le_rfl).ne', I.delta_pos.ne'] at hr ⊢
  rw [hr]

/--
Exact identity `(J.data.realization I).kernelNorm N I.mu I.mu = 2*I.epsilon N/I.delta*Real.sqrt
J.energy`.

Use: `«2610.05164v2».Jacobi.gain_lower_bound` rewrites with this identity to establish the
stated quantitative bound `2*I.epsilon N/I.delta*Real.sqrt J.energy ≤ J.gain I (J.admissible I
hN ht)`.

Article: 2610.05164v2, Corollary 1 via `«2610.05164v2».Jacobi.symmetric_gain_bounds`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem endpoint_norm (hN : 0 < N) (ht : J.Terminal) :
    (J.data.realization I).kernelNorm N I.mu I.mu =
      2*I.epsilon N/I.delta*Real.sqrt J.energy := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  have he : (∑ s ∈ Finset.range N, ((J.data.realization I).kernel N s I.mu I.mu)^2) =
      (2*I.epsilon N/I.delta)^2*J.energy := by
    rw [energy, Finset.sum_fin_eq_sum_range]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    simp only [Finset.mem_range.mp hs, dite_true]
    have hk := J.kernel_endpoint I hN ht ⟨s, Finset.mem_range.mp hs⟩
    dsimp only at hk
    rw [hk]; ring
  rw [Realization.kernelNorm, he, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
    abs_of_pos (show 0 < 2*I.epsilon N/I.delta from
      div_pos (mul_pos (by norm_num) (one_div_pos.mpr (I.den_pos N))) I.delta_pos)]

/--
The stated quantitative bound `2*I.epsilon N/I.delta*Real.sqrt J.energy ≤ J.gain I
(J.admissible I hN ht)`.

Use: `«2610.05164v2».Jacobi.gain_pos` uses this bound to establish the stated quantitative
bound `0 < J.gain I (J.admissible I hN ht)`.

Article: 2610.05164v2, Theorem 1.2 via
`«2610.05164v2».DualCertificate.uniform_sine_of_finite_lower`.

Proof: Use the identities/estimates `«2610.05164v2».Jacobi.gain_eq`,
`«2610.05164v2».Jacobi.endpoint_norm`, `«2606.16671v2».Realization.kernelNorm_le_gain` with the
arguments shown in the proof.
-/
theorem gain_lower_bound (hN : 0 < N) (ht : J.Terminal) :
    2*I.epsilon N/I.delta*Real.sqrt J.energy ≤ J.gain I (J.admissible I hN ht) := by
  rw [J.gain_eq I, ← J.endpoint_norm I hN ht]
  exact (J.data.realization I).kernelNorm_le_gain I N
    ⟨le_rfl, I.mu_lt_L.le⟩ ⟨le_rfl, I.mu_lt_L.le⟩

/--
The stated quantitative bound `0 < J.gain I (J.admissible I hN ht)`.

Use: `«2610.05164v2».Jacobi.gain_attained_dim_two` rewrites with this bound to establish the
identity stated in that declaration.

Article: 2610.05164v2, Theorem 2.2 via `«2610.05164v2».Jacobi.gain_attained_dim_two`.

Proof: Use the identities/estimates `«2606.16671v2».SpectralInterval.den_pos`,
`«2606.16671v2».SpectralInterval.delta_pos`, `«2610.05164v2».Jacobi.energy_pos` with the
arguments shown in the proof.
-/
theorem gain_pos (hN : 0 < N) (ht : J.Terminal) : 0 < J.gain I (J.admissible I hN ht) :=
  lt_of_lt_of_le (mul_pos (div_pos (mul_pos (by norm_num)
    (one_div_pos.mpr (I.den_pos N))) I.delta_pos) (Real.sqrt_pos.mpr (J.energy_pos hN ht)))
      (J.gain_lower_bound I hN ht)

/--
The gain is the sharp universal Hilbert--Schmidt coefficient, with a nonzero attaining input in
dimension two (Definition 1 and Theorem 2.2).

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Theorem 2.2.

Proof: Use the identities/estimates `«2610.05164v2».Jacobi.admissible`,
`«2606.16671v2».Realization.hs_bound_attained`, `«2610.05164v2».Jacobi.gain_pos` with the
arguments shown in the proof.
-/
theorem gain_attained_dim_two (hN : 0 < N) (ht : J.Terminal) :
    ∃ H : Matrix (Fin 2) (Fin 2) ℝ, H.IsHermitian ∧ spectrum ℝ H ⊆ Set.Icc I.mu I.L ∧
      ∃ E : ℕ → Matrix (Fin 2) (Fin 2) ℝ,
        0 < Real.sqrt (∑ s ∈ Finset.range N, hsNorm (E s)^2) ∧
        hsNorm ((J.recurrence I (J.admissible I hN ht)).method.realization.linearResponse N H E) /
          Real.sqrt (∑ s ∈ Finset.range N, hsNorm (E s)^2) = J.gain I (J.admissible I hN ht) := by
  -- Use the identities/estimates `«2610.05164v2».Jacobi.admissible`,
  -- `«2606.16671v2».Realization.hs_bound_attained`, `«2610.05164v2».Jacobi.gain_pos` with the
  -- arguments shown in the proof.
  obtain ⟨H,hH,hs,E,he,ho⟩ :=
    (J.recurrence I (J.admissible I hN ht)).method.realization.hs_bound_attained I N
  refine ⟨H,hH,hs,E,?_,?_⟩
  · rw [he]; exact J.gain_pos I hN ht
  · rw [he, ho]
    change J.gain I (J.admissible I hN ht)^2 / J.gain I (J.admissible I hN ht) = _
    rw [pow_two, mul_div_cancel_right₀ _ (J.gain_pos I hN ht).ne']

/--
Lemma 1: the trace is fixed throughout the complete Jacobi fiber.

Exact identity `Matrix.trace J.green = (N:ℝ)^2`.

Use: `«2610.05164v2».Continuum.finiteEigenvalue_sum` rewrites with this identity to establish
exact identity `(∑ j : Fin N, finiteEigenvalue N j) = 1`.

Article: 2610.05164v2, Theorem A.1.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem green_trace (hN : 0 < N) (ht : J.Terminal) : Matrix.trace J.green = (N:ℝ)^2 := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  let I : SpectralInterval := ⟨1,2,by norm_num,by norm_num⟩
  have h := J.admissible I hN ht
  have hd := (J.data.realization I).kernel_sum_derivative N I.mu
  rw [J.data.residualPolynomial_eq I h N le_rfl,
    J.data.terminal_residual I (by positivity : (2/(2:ℝ)^N) ≠ 0)
      (ht.trans (fiberPolynomial_eq N hN)), I.residual_derivative_eval_mu] at hd
  have he : (∑ s ∈ Finset.range N, (J.data.realization I).kernel N s I.mu I.mu) =
      -(2*I.epsilon N/I.delta)*Matrix.trace J.green := by
    rw [Matrix.trace, Finset.sum_fin_eq_sum_range, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    simp only [Finset.mem_range.mp hs, dite_true, Matrix.diag]
    exact J.kernel_endpoint I hN ht ⟨s,Finset.mem_range.mp hs⟩
  rw [he] at hd
  have hc : -(2*I.epsilon N/I.delta) ≠ 0 := by
    exact neg_ne_zero.mpr (div_ne_zero (mul_ne_zero (by norm_num)
      (one_div_ne_zero (I.den_ne N))) I.delta_pos.ne')
  apply mul_left_cancel₀ hc
  calc _ = _ := hd
       _ = _ := by ring

end
end «2610.05164v2».Jacobi
