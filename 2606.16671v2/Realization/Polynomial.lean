import «2606.16671v2».Realization.Expansion
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
Article: 2606.16671v2, Proposition 1.3.
The algebraic identity of Proposition 1.3 in precisely the paper's polynomial form.
Use: `«2606.16671v2».Realization.finiteDrift_polynomial_decomposition` feeds
`«2606.16671v2».Realization.static_shift_values` (The finite and first-order values in the attaining
example of Theorem 4.3(iv)).
Proof chain: `«2606.16671v2».Realization.static_shift_lower_bounds_general` — 2606.16671v2, Theorem
4.3; All insertion orders, partition bounds, finite/cosh bounds and attainment.
-/
namespace «2606.16671v2».Realization

open scoped BigOperators Kronecker Polynomial
noncomputable section

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]

omit [Fintype ι] [DecidableEq ι] in
/--
Exact identity `Polynomial.aeval H (R.polynomialStep s i j) x y = R.operatorStep s H (i, x) (j,
y)`.

Use: `«2606.16671v2».Realization.orderedProduct_polynomialStep_aeval` rewrites with this
identity to establish the identity `Polynomial.aeval H (orderedProduct R.polynomialStep n i
j) x y = orderedProduct (fun s => R.operatorStep s H) n (i, x) (j, y)`.

Article: 2606.16671v2, Theorem 2.1 via `«2606.16671v2».Prefix.operator_exact`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem polynomialStep_aeval (R : Realization ι) (s : ℕ) (H : Matrix d d ℝ)
    (i j : ι) (x y : d) :
    Polynomial.aeval H (R.polynomialStep s i j) x y = R.operatorStep s H (i, x) (j, y) := by
  simp [polynomialStep, operatorStep, queryFactor, Matrix.vecMulVec,
    Algebra.algebraMap_eq_smul_one, Matrix.kroneckerMap_apply, mul_comm, mul_assoc]

/--
Exact identity `Polynomial.aeval H (orderedProduct R.polynomialStep n i j) x y = orderedProduct
(fun s => R.operatorStep s H) n (i, x) (j, y)`.

Use: `«2606.16671v2».Realization.operatorTransfer_eq_aeval` rewrites with this identity to
establish exact identity `R.operatorTransfer n (fun _ => H) = Polynomial.aeval H
(R.residualPolynomial n)`.

Article: 2606.16671v2, Theorem 2.1 via `«2606.16671v2».Prefix.operator_exact`.

Proof: Induct on `n` while keeping `i j x y` arbitrary; the recursive step uses the
previous-stage assertion. Separate `i = j` from its negation; prove the goal under each of
these mutually exclusive hypotheses. Identify the summands/integrands on their required domain
before replacing the sum or integral.
-/
theorem orderedProduct_polynomialStep_aeval (R : Realization ι) (n : ℕ) (H : Matrix d d ℝ)
    (i j : ι) (x y : d) :
    Polynomial.aeval H (orderedProduct R.polynomialStep n i j) x y =
      orderedProduct (fun s => R.operatorStep s H) n (i, x) (j, y) := by
  -- Induct on `n` while keeping `i j x y` arbitrary; the recursive step uses the
  -- previous-stage assertion.
  induction n generalizing i j x y with
  | zero =>
    by_cases hij : i = j <;> by_cases hxy : x = y <;>
      simp [hij, hxy]
  | succ n ih =>
    simp only [orderedProduct_succ, Matrix.mul_apply, map_sum, map_mul,
      Matrix.sum_apply, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro z _
    rw [polynomialStep_aeval, ih]

/--
`T_R(H,...,H) = p_{R,n}(H)` without a spectral or positivity assumption.

Exact identity `R.operatorTransfer n (fun _ => H) = Polynomial.aeval H (R.residualPolynomial
n)`.

Use: `«2606.16671v2».Realization.finiteDrift_polynomial_decomposition` rewrites with this
identity to establish the identity `R.operatorTransfer n (fun s => H + E s) =
Polynomial.aeval H (R.residualPolynomial n) + R.linearResponse n H E + R.driftRemainder n H E`.

Article: 2606.16671v2, Theorem 2.1 via `«2606.16671v2».Prefix.operator_exact`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem operatorTransfer_eq_aeval (R : Realization ι) (n : ℕ) (H : Matrix d d ℝ) :
    R.operatorTransfer n (fun _ => H) = Polynomial.aeval H (R.residualPolynomial n) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  ext x y
  simp only [operatorTransfer, contract, residualPolynomial, map_sum, map_mul,
    Polynomial.aeval_C, Matrix.sum_apply, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, mul_smul_comm, one_mul, mul_one, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [orderedProduct_polynomialStep_aeval]
  ring

/--
The algebraic identity of Proposition 1.3 in precisely the paper's polynomial form.

Exact identity `R.operatorTransfer n (fun s => H + E s) = Polynomial.aeval H
(R.residualPolynomial n) + R.linearResponse n H E + R.driftRemainder n H E`.

Use: `«2606.16671v2».Realization.static_remainder_polynomial` uses this identity to establish
the identity stated in that declaration.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.static_shift_attained`.

Proof: Use the identities/estimates
`«2606.16671v2».Realization.operatorTransfer_decomposition`,
`«2606.16671v2».Realization.operatorTransfer_eq_aeval` with the arguments shown in the proof.
-/
theorem finiteDrift_polynomial_decomposition (R : Realization ι) (n : ℕ) (H : Matrix d d ℝ)
    (E : ℕ → Matrix d d ℝ) :
    R.operatorTransfer n (fun s => H + E s) =
      Polynomial.aeval H (R.residualPolynomial n) + R.linearResponse n H E +
        R.driftRemainder n H E := by rw [operatorTransfer_decomposition, operatorTransfer_eq_aeval]

end
end «2606.16671v2».Realization
