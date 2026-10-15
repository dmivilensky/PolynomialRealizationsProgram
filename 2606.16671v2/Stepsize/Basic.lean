import «2606.16671v2».Realization.GainBounds
import «2606.16671v2».Chebyshev.Polynomial

/-!
Article: 2606.16671v2, Theorem 1.4.
A product of affine factors satisfies this exact diagonal-kernel identity.
Use: `«2606.16671v2».Stepsize.kernel_square_sum_derivatives` feeds
`«2606.16671v2».Stepsize.endpoint_square_sum` (The endpoint energy is independent of the ordering of
an exact schedule).
Proof chain: `«2606.16671v2».Stepsize.endpoint_square_sum` — 2606.16671v2, Theorem 1.4; Sharp
stepsize drift lower bound and asymptotics.
-/
namespace «2606.16671v2».Stepsize
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped Polynomial BigOperators

/--
Constructs `realization` of type `Realization Unit` by the displayed record fields. Data fields
specify the construction; proof fields discharge its required properties.

Use: `«2606.16671v2».Stepsize.FinalExact` uses this definition in the displayed construction of
`FinalExact`. Its inputs and component formulas are fixed by that definition.

Article: 2606.16671v2, Theorem 1.4 via `«2606.16671v2».Stepsize.endpoint_square_sum`.
-/
def realization (gamma : ℕ → ℝ) : Realization Unit where
  b := fun _ => 1
  readout := fun _ => 1
  P := fun _ => 1
  g := fun s _ => gamma s
  q := fun _ _ => 1

/--
Defines `polynomial` by pattern matching with result type `ℕ → ℝ[X]`. The displayed branches
determine the recursive cases and their returned values.

Use: `«2606.16671v2».Stepsize.kernel_square_sum_derivatives` rewrites with this definition to
establish the identity stated in that declaration.

Article: 2606.16671v2, Theorem 1.4 via `«2606.16671v2».Stepsize.endpoint_square_sum`.
-/
def polynomial (gamma : ℕ → ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (1 - C (gamma n) * X) * polynomial gamma n

/--
Defines `FinalExact` of type `Prop` by `∀ lam ∈ Set.Icc I.mu I.L, (realization
gamma).scalarTransfer N lam = (I.residual N).eval lam`.

Use: `«2606.16671v2».Stepsize.final_polynomial_eq` uses this definition to establish exact
identity `polynomial gamma N = I.residual N`.

Article: 2606.16671v2, Theorem 1.4 via `«2606.16671v2».Stepsize.endpoint_square_sum`.
-/
def FinalExact (gamma : ℕ → ℝ) (I : SpectralInterval) (N : ℕ) : Prop :=
  ∀ lam ∈ Set.Icc I.mu I.L,
    (realization gamma).scalarTransfer N lam = (I.residual N).eval lam

/--
Exact identity `orderedProduct (A := Matrix Unit Unit ℝ) (fun s => fun (_ _ : Unit) => c s) n
() () = orderedProduct c n`.

Use: `«2606.16671v2».Stepsize.kernel_formula` rewrites with this identity to establish exact
identity `(realization gamma).kernel N s lam nu = -(orderedProduct (fun i => 1 - gamma (s + 1 +
i) * lam) (N - (s + 1)) * gamma s * orderedProduct (fun i => 1 - gamma i * nu) s)`.

Article: 2606.16671v2, Theorem 1.4 via `«2606.16671v2».Stepsize.endpoint_square_sum`.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
private theorem product_entry (c : ℕ → ℝ) (n : ℕ) :
    orderedProduct (A := Matrix Unit Unit ℝ) (fun s => fun (_ _ : Unit) => c s) n () () = orderedProduct c n := by
  induction n with
  | zero => simp [orderedProduct]
  | succ n ih => simp [orderedProduct, Matrix.mul_apply, ih]

/--
Exact identity `(realization gamma).scalarContract M = M () ()`.

Use: `«2606.16671v2».Stepsize.kernel_formula` rewrites with this identity to establish exact
identity `(realization gamma).kernel N s lam nu = -(orderedProduct (fun i => 1 - gamma (s + 1 +
i) * lam) (N - (s + 1)) * gamma s * orderedProduct (fun i => 1 - gamma i * nu) s)`.

Article: 2606.16671v2, Theorem 1.4 via `«2606.16671v2».Stepsize.endpoint_square_sum`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[simp] theorem scalarContract (gamma : ℕ → ℝ) (M : Matrix Unit Unit ℝ) :
    (realization gamma).scalarContract M = M () () := by simp [Realization.scalarContract, realization]

/--
Exact identity `(realization gamma).scalarStep s lam = fun (_ _ : Unit) => 1 - gamma s * lam`.

Use: `«2606.16671v2».Stepsize.kernel_formula` rewrites with this identity to establish exact
identity `(realization gamma).kernel N s lam nu = -(orderedProduct (fun i => 1 - gamma (s + 1 +
i) * lam) (N - (s + 1)) * gamma s * orderedProduct (fun i => 1 - gamma i * nu) s)`.

Article: 2606.16671v2, Theorem 1.4 via `«2606.16671v2».Stepsize.endpoint_square_sum`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem scalarStep_eq (gamma : ℕ → ℝ) (s : ℕ) (lam : ℝ) :
    (realization gamma).scalarStep s lam = fun (_ _ : Unit) => 1 - gamma s * lam := by
  ext i j
  cases i; cases j
  simp [Realization.scalarStep, Realization.queryFactor, realization, Matrix.vecMulVec,
    Matrix.sub_apply, mul_comm]

/--
Exact identity `(realization gamma).scalarTransfer n lam = orderedProduct (fun s => 1 - gamma s
* lam) n`.

Use: `«2606.16671v2».Stepsize.kernel_last` rewrites with this identity to establish exact
identity `(realization gamma).kernel (N + 1) N lam nu = -gamma N * (polynomial gamma N).eval
nu`.

Article: 2606.16671v2, Theorem 1.4 via `«2606.16671v2».Stepsize.endpoint_square_sum`.

Proof: Use the identities/estimates `«2606.16671v2».Stepsize.scalarContract`,
`«2606.16671v2».Stepsize.scalarStep_eq`,
`_private.«2606.16671v2».Stepsize.Basic.0.«2606.16671v2».Stepsize.product_entry` with the
arguments shown in the proof.
-/
theorem scalarTransfer_eq (gamma : ℕ → ℝ) (n : ℕ) (lam : ℝ) :
    (realization gamma).scalarTransfer n lam =
      orderedProduct (fun s => 1 - gamma s * lam) n := by
  rw [Realization.scalarTransfer, scalarContract]
  simp_rw [scalarStep_eq]
  exact product_entry _ _

/--
Exact identity `(polynomial gamma n).eval lam = (realization gamma).scalarTransfer n lam`.

Use: `«2606.16671v2».Stepsize.final_polynomial_eq` rewrites with this identity to establish
exact identity `polynomial gamma N = I.residual N`.

Article: 2606.16671v2, Theorem 1.4 via `«2606.16671v2».Stepsize.endpoint_square_sum`.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem polynomial_eval (gamma : ℕ → ℝ) (n : ℕ) (lam : ℝ) :
    (polynomial gamma n).eval lam = (realization gamma).scalarTransfer n lam := by
  rw [scalarTransfer_eq]
  induction n with
  | zero => simp [polynomial, orderedProduct]
  | succ n ih => simp [polynomial, orderedProduct, ih]

/--
Exact identity `(realization gamma).residualPolynomial n = polynomial gamma n`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2606.16671v2, Theorem 1.4.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem residualPolynomial_eq (gamma : ℕ → ℝ) (n : ℕ) :
    (realization gamma).residualPolynomial n = polynomial gamma n := by
  apply Polynomial.funext
  intro lam
  rw [Realization.residualPolynomial_eval, polynomial_eval]

/--
Exact identity `polynomial gamma N = I.residual N`.

Use: `«2606.16671v2».Stepsize.endpoint_square_sum` rewrites with this identity to establish
exact identity `(∑ s ∈ Finset.range N, ((realization gamma).kernel N s I.mu I.mu) ^ 2) = (2 *
I.epsilon N / I.delta) ^ 2 * (((2 : ℝ) * N ^ 4 + N ^ 2) / 3)`.

Article: 2606.16671v2, Theorem 1.4 via `«2606.16671v2».Stepsize.endpoint_square_sum`.

Proof: Use the identities/estimates `«2606.16671v2».SpectralInterval.polynomial_eq`,
`«2606.16671v2».Stepsize.polynomial_eval` with the arguments shown in the proof.
-/
theorem final_polynomial_eq (gamma : ℕ → ℝ) (I : SpectralInterval) (N : ℕ)
    (h : FinalExact gamma I N) : polynomial gamma N = I.residual N := by
  apply I.polynomial_eq
  intro lam hl
  rw [polynomial_eval]
  exact h lam hl

/--
Exact identity `(realization gamma).kernel N s lam nu = -(orderedProduct (fun i => 1 - gamma (s
+ 1 + i) * lam) (N - (s + 1)) * gamma s * orderedProduct (fun i => 1 - gamma i * nu) s)`.

Use: `«2606.16671v2».Stepsize.kernel_extend` rewrites with this identity to establish exact
identity `(realization gamma).kernel (N + 1) s lam nu = (1 - gamma N * lam) * (realization
gamma).kernel N s lam nu`.

Article: 2606.16671v2, Theorem 1.4 via `«2606.16671v2».Stepsize.endpoint_square_sum`.

Proof: Use the identities/estimates `«2606.16671v2».Stepsize.scalarContract`,
`«2606.16671v2».Stepsize.scalarStep_eq`,
`_private.«2606.16671v2».Stepsize.Basic.0.«2606.16671v2».Stepsize.product_entry` with the
arguments shown in the proof.
-/
theorem kernel_formula (gamma : ℕ → ℝ) (N s : ℕ) (lam nu : ℝ) :
    (realization gamma).kernel N s lam nu =
      -(orderedProduct (fun i => 1 - gamma (s + 1 + i) * lam) (N - (s + 1)) *
        gamma s * orderedProduct (fun i => 1 - gamma i * nu) s) := by
  -- Use the identities/estimates `«2606.16671v2».Stepsize.scalarContract`,
  -- `«2606.16671v2».Stepsize.scalarStep_eq`,
  -- `_private.«2606.16671v2».Stepsize.Basic.0.«2606.16671v2».Stepsize.product_entry` with the
  -- arguments shown in the proof.
  rw [Realization.kernel, scalarContract]
  simp_rw [scalarStep_eq]
  simp only [Matrix.mul_apply, Fintype.sum_unique]
  rw [product_entry, product_entry]
  simp [Realization.queryFactor, realization, Matrix.vecMulVec]

/--
Exact identity `(realization gamma).kernel (N + 1) s lam nu = (1 - gamma N * lam) *
(realization gamma).kernel N s lam nu`.

Use: `«2606.16671v2».Stepsize.kernel_square_sum_extend` rewrites with this identity to
establish the identity stated in that declaration.

Article: 2606.16671v2, Theorem 1.4 via `«2606.16671v2».Stepsize.endpoint_square_sum`.

Proof: Use the identities/estimates `«2606.16671v2».Stepsize.kernel_formula`,
`«2606.16671v2».orderedProduct_succ` with the arguments shown in the proof.
-/
theorem kernel_extend (gamma : ℕ → ℝ) (N s : ℕ) (hs : s < N) (lam nu : ℝ) :
    (realization gamma).kernel (N + 1) s lam nu =
      (1 - gamma N * lam) * (realization gamma).kernel N s lam nu := by
  rw [kernel_formula, kernel_formula]
  have hlength : N + 1 - (s + 1) = (N - (s + 1)) + 1 := by omega
  rw [hlength, orderedProduct_succ, show s + 1 + (N - (s + 1)) = N by omega]
  ring

/--
Exact identity `(realization gamma).kernel (N + 1) N lam nu = -gamma N * (polynomial gamma
N).eval nu`.

Use: `«2606.16671v2».Stepsize.kernel_square_sum_extend` rewrites with this identity to
establish the identity stated in that declaration.

Article: 2606.16671v2, Theorem 1.4 via `«2606.16671v2».Stepsize.endpoint_square_sum`.

Proof: Use the identities/estimates `«2606.16671v2».Stepsize.kernel_formula`,
`«2606.16671v2».Stepsize.polynomial_eval`, `«2606.16671v2».Stepsize.scalarTransfer_eq` with the
arguments shown in the proof.
-/
theorem kernel_last (gamma : ℕ → ℝ) (N : ℕ) (lam nu : ℝ) :
    (realization gamma).kernel (N + 1) N lam nu =
      -gamma N * (polynomial gamma N).eval nu := by
  rw [kernel_formula, polynomial_eval, scalarTransfer_eq]
  simp

/--
Exact identity `(∑ s ∈ Finset.range (N + 1), ((realization gamma).kernel (N + 1) s lam lam) ^
2) = (1 - gamma N * lam) ^ 2 * (∑ s ∈ Finset.range N, ((realization gamma).kernel N s lam lam)
^ 2) + (gamma N) ^ 2 * ((polynomial gamma N).eval lam) ^ 2`.

Use: `«2606.16671v2».Stepsize.kernel_square_sum_derivatives` rewrites with this identity to
establish the identity stated in that declaration.

Article: 2606.16671v2, Theorem 1.4 via `«2606.16671v2».Stepsize.endpoint_square_sum`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem kernel_square_sum_extend (gamma : ℕ → ℝ) (N : ℕ) (lam : ℝ) :
    (∑ s ∈ Finset.range (N + 1), ((realization gamma).kernel (N + 1) s lam lam) ^ 2) =
      (1 - gamma N * lam) ^ 2 *
        (∑ s ∈ Finset.range N, ((realization gamma).kernel N s lam lam) ^ 2) +
      (gamma N) ^ 2 * ((polynomial gamma N).eval lam) ^ 2 := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  rw [Finset.sum_range_succ, kernel_last]
  have hterm (s : ℕ) (hs : s ∈ Finset.range N) :
      ((realization gamma).kernel (N + 1) s lam lam) ^ 2 =
        (1 - gamma N * lam) ^ 2 * ((realization gamma).kernel N s lam lam) ^ 2 := by
    rw [kernel_extend gamma N s (Finset.mem_range.mp hs), mul_pow]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  ring

/--
A product of affine factors satisfies this exact diagonal-kernel identity.

Exact identity `(∑ s ∈ Finset.range N, ((realization gamma).kernel N s lam lam) ^ 2) =
((polynomial gamma N).derivative.eval lam) ^ 2 - (polynomial gamma N).eval lam * (polynomial
gamma N).derivative.derivative.eval lam`.

Use: `«2606.16671v2».Stepsize.endpoint_square_sum` rewrites with this identity to establish
exact identity `(∑ s ∈ Finset.range N, ((realization gamma).kernel N s I.mu I.mu) ^ 2) = (2 *
I.epsilon N / I.delta) ^ 2 * (((2 : ℝ) * N ^ 4 + N ^ 2) / 3)`.

Article: 2606.16671v2, Theorem 1.4 via `«2606.16671v2».Stepsize.endpoint_square_sum`.

Proof: Induct on `N`; the recursive step uses the previous-stage assertion.
-/
theorem kernel_square_sum_derivatives (gamma : ℕ → ℝ) (N : ℕ) (lam : ℝ) :
    (∑ s ∈ Finset.range N, ((realization gamma).kernel N s lam lam) ^ 2) =
      ((polynomial gamma N).derivative.eval lam) ^ 2 -
      (polynomial gamma N).eval lam * (polynomial gamma N).derivative.derivative.eval lam := by
  -- Induct on `N`; the recursive step uses the previous-stage assertion.
  induction N with
  | zero => simp [polynomial]
  | succ N ih =>
    rw [kernel_square_sum_extend, ih]
    simp only [polynomial, derivative_mul, derivative_sub, derivative_one,
      derivative_C, derivative_X, zero_mul, mul_one, zero_add, derivative_add,
      eval_add, eval_sub, eval_mul, eval_one, eval_C,
      eval_X, derivative_zero, eval_zero]
    ring

end
end «2606.16671v2».Stepsize
