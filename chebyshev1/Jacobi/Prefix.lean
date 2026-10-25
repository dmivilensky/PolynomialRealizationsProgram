import chebyshev1.Jacobi.Kernel

/-!
Article: chebyshev1, Corollary 4.4.
The maximum property needed in Theorem 4.3(iii), including empty blocks.
Use: `chebyshev1.Prefix.jacobiBlock_endpoint_max` feeds
`chebyshev1.Prefix.jacobi_endpointMax` (jacobi endpoint Max).
Proof chain: `chebyshev1.Prefix.opNorm_linearResponse_le` — chebyshev1, Corollary 4.4;
Attained finite-drift bounds for the prefix recurrence.
-/
namespace chebyshev1.Prefix
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped Matrix

/--
The Jacobi data of Corollary 4.4; site zero has no left coupling.

Use: `chebyshev1.Prefix.jacobiBlock` uses this definition in the displayed construction of
`jacobiBlock`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.
-/
def jacobiData : JacobiData where
  b := fun _ => 0
  aSq := fun s => if s = 0 then 0 else if s = 1 then 1 / 2 else 1 / 4

/--
Exact identity `jacobiData.b s = 0`.

Use: registered as a simplification rule for the displayed expression. The rule remains
available even when kernel reduction eliminates an explicit reference to this lemma.

Article: chebyshev1, Corollary 4.4.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
@[simp] theorem jacobiData_b (s : ℕ) : jacobiData.b s = 0 := rfl
/--
Exact identity `jacobiData.aSq 1 = 1 / 2`.

Use: registered as a simplification rule for the displayed expression. The rule remains
available even when kernel reduction eliminates an explicit reference to this lemma.

Article: chebyshev1, Corollary 4.4.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
@[simp] theorem jacobiData_aSq_one : jacobiData.aSq 1 = 1 / 2 := rfl

/--
Exact identity `jacobiData.aSq s = 1 / 4`.

Use: `chebyshev1.Prefix.jacobi_b_succ` rewrites with this identity to establish exact
identity `(jacobiData.method I).b (n + 1) = -(I.den n / I.den (n + 2))`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem jacobiData_aSq (s : ℕ) (hs : 2 ≤ s) : jacobiData.aSq s = 1 / 4 := by simp [jacobiData, show s ≠ 0 by omega, show s ≠ 1 by omega]

/--
Exact identity `jacobiData.leading (n + 1) = C ((1 / 2 : ℝ) ^ n) * T ℝ (n + 1)`.

Use: `chebyshev1.Prefix.jacobiBlock_leading` rewrites with this identity to establish exact
identity `jacobiBlock 0 (n + 1) = C 2 * T ℝ (n + 1)`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_finiteDrift_le`.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion. Prove equality of
functions by evaluating both sides at an arbitrary argument.
-/
theorem jacobi_leading (n : ℕ) :
    jacobiData.leading (n + 1) = C ((1 / 2 : ℝ) ^ n) * T ℝ (n + 1) := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  induction n using Nat.twoStepInduction with
  | zero => simp [JacobiData.leading, JacobiData.block, jacobiData]
  | one =>
    apply Polynomial.funext
    intro x
    simp [JacobiData.leading, JacobiData.block, jacobiData, T_two]
    ring_nf
  | more n ih0 ih1 =>
    have hr : jacobiData.leading (n + 3) = X * jacobiData.leading (n + 2) -
        C (1 / 4) * jacobiData.leading (n + 1) := by
      simp [JacobiData.leading, JacobiData.block, jacobiData_aSq]
    rw [hr, ih1, ih0]
    simp only [Nat.cast_add, Nat.cast_ofNat]
    rw [show (n : ℤ) + 2 + 1 = ((n : ℤ) + 1) + 2 by omega, T_add_two]
    apply Polynomial.funext
    intro x
    simp only [eval_sub, eval_mul, eval_C, eval_X, eval_ofNat, pow_succ]
    ring_nf

/--
Every block strictly to the right of the first site is a scaled U polynomial.

Exact identity `jacobiData.block a n = C ((1 / 2 : ℝ) ^ n) * U ℝ n`.

Use: `chebyshev1.Prefix.jacobiBlock_interior` rewrites with this identity to establish
exact identity `jacobiBlock a n = U ℝ n`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion. Prove equality of
functions by evaluating both sides at an arbitrary argument.
-/
theorem jacobi_interior (a n : ℕ) (ha : 1 ≤ a) :
    jacobiData.block a n = C ((1 / 2 : ℝ) ^ n) * U ℝ n := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  induction n using Nat.twoStepInduction with
  | zero => simp [JacobiData.block]
  | one =>
    apply Polynomial.funext
    intro x
    simp [JacobiData.block, jacobiData, U_one]
  | more n ih0 ih1 =>
    rw [JacobiData.block]
    simp only [jacobiData_aSq (a + n + 1) (by omega)]
    change (X - C 0) * jacobiData.block a (n + 1) - C (1 / 4) * jacobiData.block a n = _
    rw [ih1, ih0]
    simp only [Nat.cast_add, Nat.cast_ofNat, U_add_two]
    apply Polynomial.funext
    intro x
    simp only [eval_sub, eval_mul, eval_C, eval_X, eval_ofNat, pow_succ]
    ring_nf

/--
Exact identity `jacobiData.den I (n + 1) = (1 / 2 : ℝ) ^ n * I.den (n + 1)`.

Use: `chebyshev1.Prefix.jacobi_a_succ` rewrites with this identity to establish exact
identity `(jacobiData.method I).a (n + 1) = 2 * I.eta * I.den (n + 1) / I.den (n + 2)`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.

Proof: Use the identities/estimates `chebyshev1.Prefix.jacobi_leading` with the arguments
shown in the proof.
-/
theorem jacobi_den (I : SpectralInterval) (n : ℕ) :
    jacobiData.den I (n + 1) = (1 / 2 : ℝ) ^ n * I.den (n + 1) := by simp [JacobiData.den, jacobi_leading, SpectralInterval.den]

/--
The precise assertion is `jacobiData.Admissible I N`.

Use: `chebyshev1.Prefix.opNorm_driftRemainder_cosh_le` uses this assertion to establish the
stated quantitative bound `opNorm ((realization I).driftRemainder N H E) ≤ (2/3:ℝ)*I.epsilon
N*(N:ℝ)^4*(delta/I.delta)^2 * Real.cosh (2*(N:ℝ)*Real.sqrt (delta/I.delta))`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.

Proof: Use the identities/estimates `chebyshev1.Prefix.jacobi_den`,
`chebyshev1.SpectralInterval.den_pos` with the arguments shown in the proof.
-/
theorem jacobi_admissible (I : SpectralInterval) (N : ℕ) : jacobiData.Admissible I N := by
  intro n _
  cases n with
  | zero => simp
  | succ n => rw [jacobi_den]; exact mul_pos (by positivity) (I.den_pos (n + 1))

/--
Exact identity `(jacobiData.method I).a (n + 1) = 2 * I.eta * I.den (n + 1) / I.den (n + 2)`.

Use: `chebyshev1.Prefix.jacobi_realization` rewrites with this identity to establish exact
identity `jacobiData.realization I = realization I`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem jacobi_a_succ (I : SpectralInterval) (n : ℕ) :
    (jacobiData.method I).a (n + 1) = 2 * I.eta * I.den (n + 1) / I.den (n + 2) := by
  simp only [JacobiData.method, jacobiData_b, sub_zero, jacobi_den]
  field_simp [I.den_ne (n + 2), pow_ne_zero n (by norm_num : (1 / 2 : ℝ) ≠ 0), pow_succ]
  ring

/--
Exact identity `(jacobiData.method I).b (n + 1) = -(I.den n / I.den (n + 2))`.

Use: `chebyshev1.Prefix.jacobi_realization` rewrites with this identity to establish exact
identity `jacobiData.realization I = realization I`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem jacobi_b_succ (I : SpectralInterval) (n : ℕ) :
    (jacobiData.method I).b (n + 1) = -(I.den n / I.den (n + 2)) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  simp only [JacobiData.method, Nat.add_sub_cancel]
  cases n with
  | zero =>
    simp only [Nat.zero_add, jacobiData_aSq_one, JacobiData.den_zero, I.den_zero]
    rw [show (2 : ℕ) = 1 + 1 by rfl, jacobi_den]
    field_simp [I.den_ne 2]
  | succ n =>
    rw [jacobiData_aSq (n + 1 + 1) (by omega)]
    simp only [jacobi_den]
    field_simp [I.den_ne (n + 1 + 2), pow_ne_zero n (by norm_num : (1 / 2 : ℝ) ≠ 0), pow_succ]
    ring

/--
Exact identity `(jacobiData.method I).gamma n = gamma I n`.

Use: `chebyshev1.Prefix.jacobi_realization` rewrites with this identity to establish exact
identity `jacobiData.realization I = realization I`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem jacobi_gamma (I : SpectralInterval) (n : ℕ) :
    (jacobiData.method I).gamma n = gamma I n := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  cases n with
  | zero =>
    simp only [JacobiData.method, Nat.zero_add, JacobiData.den_zero, JacobiData.den_one, jacobiData_b,
      sub_zero, mul_one, gamma]
    dsimp [SpectralInterval.eta]
    field_simp [ne_of_gt I.delta_pos, ne_of_gt I.sum_pos]
  | succ n =>
    simp only [JacobiData.method, jacobi_den, gamma]
    field_simp [I.den_ne (n + 2), ne_of_gt I.delta_pos,
      pow_ne_zero n (by norm_num : (1 / 2 : ℝ) ≠ 0), pow_succ]
    ring

/--
Corollary 4.4 identifies the realization itself, hence also every drift term.

Exact identity `jacobiData.realization I = realization I`.

Use: `chebyshev1.Nonlinear.MethodFamily.finiteDrift_le` rewrites with this identity to
establish the stated quantitative bound `opNorm (((family.data N).realization
I).operatorTransfer N (fun s => H+E s) - aeval H (I.residual N)) ≤ I.epsilon N * ((T ℝ N).eval
(1+2*delta/I.delta)-1)`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem jacobi_realization (I : SpectralInterval) : jacobiData.realization I = realization I := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  unfold JacobiData.realization TwoTerm.realization realization
  congr 1
  · funext n
    cases n with
    | zero => simp
    | succ n => simp [jacobi_a_succ, jacobi_b_succ]
  · funext n
    rw [jacobi_gamma]

/--
Normalized blocks, with empty blocks equal to one.

Use: `chebyshev1.Prefix.jacobiBlock_endpoint_max` rewrites with this definition to
establish the stated quantitative bound `|(jacobiBlock a n).eval x| ≤ (jacobiBlock a n).eval
1`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.
-/
def jacobiBlock (a n : ℕ) : ℝ[X] := C ((2 : ℝ) ^ n) * jacobiData.block a n

/--
Exact identity `jacobiBlock 0 (n + 1) = C 2 * T ℝ (n + 1)`.

Use: `chebyshev1.Prefix.jacobiBlock_endpoint_max` rewrites with this identity to establish
the stated quantitative bound `|(jacobiBlock a n).eval x| ≤ (jacobiBlock a n).eval 1`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.

Proof: Use the identities/estimates `chebyshev1.Prefix.jacobi_leading` with the arguments
shown in the proof.
-/
theorem jacobiBlock_leading (n : ℕ) : jacobiBlock 0 (n + 1) = C 2 * T ℝ (n + 1) := by
  change C ((2 : ℝ) ^ (n + 1)) * jacobiData.leading (n + 1) = _
  rw [jacobi_leading, ← mul_assoc, ← map_mul]
  have hc : (2 : ℝ) ^ (n + 1) * (1 / 2) ^ n = 2 := by
    rw [pow_succ]; calc _ = 2 * (2 * (1 / 2 : ℝ)) ^ n := by rw [mul_pow]; ring
                       _ = 2 := by norm_num
  rw [hc]

/--
Exact identity `jacobiBlock a n = U ℝ n`.

Use: `chebyshev1.Prefix.jacobiBlock_endpoint_max` rewrites with this identity to establish
the stated quantitative bound `|(jacobiBlock a n).eval x| ≤ (jacobiBlock a n).eval 1`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.

Proof: Use the identities/estimates `chebyshev1.Prefix.jacobi_interior` with the arguments
shown in the proof.
-/
theorem jacobiBlock_interior (a n : ℕ) (ha : 1 ≤ a) : jacobiBlock a n = U ℝ n := by
  rw [jacobiBlock, jacobi_interior a n ha, ← mul_assoc, ← map_mul, ← mul_pow]
  norm_num

/--
The maximum property needed in Theorem 4.3(iii), including empty blocks.

The stated quantitative bound `|(jacobiBlock a n).eval x| ≤ (jacobiBlock a n).eval 1`.

Use: `chebyshev1.Prefix.jacobi_endpointMax` uses this bound to establish the precise
assertion is `jacobiData.EndpointMax N`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.

Proof: Use the identities/estimates `chebyshev1.Prefix.jacobiBlock_leading`,
`chebyshev1.Prefix.jacobiBlock_interior`, `chebyshev1.abs_U_eval_le` with the arguments
shown in the proof.
-/
theorem jacobiBlock_endpoint_max (a n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    |(jacobiBlock a n).eval x| ≤ (jacobiBlock a n).eval 1 := by
  -- Use the identities/estimates `chebyshev1.Prefix.jacobiBlock_leading`,
  -- `chebyshev1.Prefix.jacobiBlock_interior`, `chebyshev1.abs_U_eval_le` with the
  -- arguments shown in the proof.
  cases a with
  | zero =>
    cases n with
    | zero => simp [jacobiBlock, JacobiData.block]
    | succ n =>
      rw [jacobiBlock_leading]
      simp only [eval_mul, eval_C, T_eval_one, mul_one, abs_mul,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      simpa using mul_le_mul_of_nonneg_left
        (abs_eval_T_real_le_one (n + 1) (abs_le.mpr hx)) (by norm_num : (0 : ℝ) ≤ 2)
  | succ a =>
    rw [jacobiBlock_interior (a + 1) n (by omega)]
    simpa using abs_U_eval_le n (abs_le.mpr hx)

end
end chebyshev1.Prefix
