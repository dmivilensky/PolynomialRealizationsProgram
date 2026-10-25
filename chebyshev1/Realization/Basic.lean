import chebyshev1.Algebra.OrderedProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
Article: chebyshev1, Definition 1.2.
Input/output contraction is linear in the memory-space operator.
Use: `chebyshev1.Realization.operatorTransfer` feeds
`chebyshev1.Realization.kernel_sum_derivative` (The sum of all insertion kernels is the
derivative under a static spectral shift).
Proof chain: `chebyshev1.Prefix.operator_exact` — chebyshev1, Theorem 2.1; Prefix-exact
recurrence and quadratic transfer.
-/
namespace chebyshev1

noncomputable section

open scoped BigOperators Kronecker Polynomial

/--
The data `(b, ℓ, P_s, g_s, q_s)` of Section 1.

Use: `chebyshev1.Realization.operatorInsertion_smul` uses this record of data and proof
obligations to establish the identity `R.operatorInsertion s (δ • E) = δ •
R.operatorInsertion s E`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.
-/
structure Realization (ι : Type*) where
  /-- Initial memory vector multiplying the initial physical error. -/
  b : ι → ℝ
  /-- Linear functional selecting the terminal physical error from memory. -/
  readout : ι → ℝ
  /-- Unperturbed memory transition matrix at each iteration. -/
  P : ℕ → Matrix ι ι ℝ
  /-- Injection vector for the Hessian/query correction at each iteration. -/
  g : ℕ → ι → ℝ
  /-- Query vector selecting which memory combination the Hessian acts on. -/
  q : ℕ → ι → ℝ

namespace Realization

variable {ι d : Type*} [Fintype ι] [DecidableEq ι]

/--
The rank-one gradient-query factor `g_s q_sᵀ`.

Use: `chebyshev1.Realization.kernel` uses this definition in the displayed construction of
`kernel`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev1, Theorem 3.1 via `chebyshev1.TwoTerm.kernel_eq_prefix`.
-/
def queryFactor (R : Realization ι) (s : ℕ) : Matrix ι ι ℝ :=
  Matrix.vecMulVec (R.g s) (R.q s)

/--
The scalar spectral pencil `C_s(lam)`.

Use: `chebyshev1.Realization.polynomialStep_eval` rewrites with this definition to
establish exact identity `(R.polynomialStep s).map (Polynomial.eval lam) = R.scalarStep s lam`.

Article: chebyshev1, Theorem 2.2 via `chebyshev1.Prefix.kernel_zero`.
-/
def scalarStep (R : Realization ι) (s : ℕ) (lam : ℝ) : Matrix ι ι ℝ :=
  R.P s - lam • R.queryFactor s

/--
Input/output contraction in scalar spectral coordinates.

Use: `chebyshev1.Realization.kernel` uses this definition in the displayed construction of
`kernel`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev1, Theorem 3.1 via `chebyshev1.TwoTerm.kernel_eq_prefix`.
-/
def scalarContract (R : Realization ι) (M : Matrix ι ι ℝ) : ℝ :=
  ∑ i, ∑ j, R.readout i * M i j * R.b j

/--
Defines `scalarTransfer` of type `ℝ` by `R.scalarContract (orderedProduct (fun s =>
R.scalarStep s lam) n)`.

Use: `chebyshev1.Realization.residualPolynomial_eval` rewrites with this definition to
establish exact identity `(R.residualPolynomial n).eval lam = R.scalarTransfer n lam`.

Article: chebyshev1, Theorem 2.1 via `chebyshev1.Prefix.residualPolynomial_eq`.
-/
def scalarTransfer (R : Realization ι) (n : ℕ) (lam : ℝ) : ℝ :=
  R.scalarContract (orderedProduct (fun s => R.scalarStep s lam) n)

/--
A polynomial matrix, so terminal exactness is an equality of polynomials.

Use: `chebyshev1.Realization.orderedProduct_polynomialStep_eval` rewrites with this
definition to establish the identity `(orderedProduct R.polynomialStep n).map
(Polynomial.eval lam) = orderedProduct (fun s => R.scalarStep s lam) n`.

Article: chebyshev1, Theorem 2.1 via `chebyshev1.Prefix.residualPolynomial_eq`.
-/
def polynomialStep (R : Realization ι) (s : ℕ) : Matrix ι ι ℝ[X] :=
  fun i j => Polynomial.C (R.P s i j) -
    Polynomial.X * Polynomial.C (R.g s i * R.q s j)

/--
Defines `residualPolynomial` of type `ℝ[X]` by `∑ i, ∑ j, Polynomial.C (R.readout i) *
orderedProduct R.polynomialStep n i j * Polynomial.C (R.b j)`.

Use: `chebyshev1.Realization.residualPolynomial_eval` rewrites with this definition to
establish exact identity `(R.residualPolynomial n).eval lam = R.scalarTransfer n lam`.

Article: chebyshev1, Theorem 2.1 via `chebyshev1.Prefix.residualPolynomial_eq`.
-/
def residualPolynomial (R : Realization ι) (n : ℕ) : ℝ[X] :=
  ∑ i, ∑ j, Polynomial.C (R.readout i) *
    orderedProduct R.polynomialStep n i j * Polynomial.C (R.b j)

omit [Fintype ι] [DecidableEq ι] in
/--
Exact identity `(R.polynomialStep s).map (Polynomial.eval lam) = R.scalarStep s lam`.

Use: `chebyshev1.Realization.orderedProduct_polynomialStep_eval` rewrites with this
identity to establish the identity `(orderedProduct R.polynomialStep n).map (Polynomial.eval
lam) = orderedProduct (fun s => R.scalarStep s lam) n`.

Article: chebyshev1, Theorem 2.1 via `chebyshev1.Prefix.residualPolynomial_eq`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem polynomialStep_eval (R : Realization ι) (s : ℕ) (lam : ℝ) :
    (R.polynomialStep s).map (Polynomial.eval lam) = R.scalarStep s lam := by
  ext i j
  simp [polynomialStep, scalarStep, queryFactor, Matrix.vecMulVec]

/--
Exact identity `(orderedProduct R.polynomialStep n).map (Polynomial.eval lam) = orderedProduct
(fun s => R.scalarStep s lam) n`.

Use: `chebyshev1.Realization.residualPolynomial_eval` uses this identity to establish exact
identity `(R.residualPolynomial n).eval lam = R.scalarTransfer n lam`.

Article: chebyshev1, Theorem 2.1 via `chebyshev1.Prefix.residualPolynomial_eq`.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion. Separate `i = j`
from its negation; prove the goal under each of these mutually exclusive hypotheses.
-/
theorem orderedProduct_polynomialStep_eval (R : Realization ι) (n : ℕ) (lam : ℝ) :
    (orderedProduct R.polynomialStep n).map (Polynomial.eval lam) =
      orderedProduct (fun s => R.scalarStep s lam) n := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  induction n with
  | zero => ext i j; by_cases h : i = j <;> simp [h]
  | succ n ih =>
    rw [orderedProduct_succ, orderedProduct_succ]
    rw [show (R.polynomialStep n * orderedProduct R.polynomialStep n).map
        (Polynomial.eval lam) = (R.polynomialStep n).map (Polynomial.eval lam) *
        (orderedProduct R.polynomialStep n).map (Polynomial.eval lam) from
      Matrix.map_mul (f := Polynomial.evalRingHom lam)]
    rw [polynomialStep_eval, ih]

/--
The transfer defined by the ordered realization evaluates its residual polynomial.

Exact identity `(R.residualPolynomial n).eval lam = R.scalarTransfer n lam`.

Use: `chebyshev1.JacobiData.residualPolynomial_eq` rewrites with this identity to establish
exact identity `(J.realization I).residualPolynomial n = J.residual I n`.

Article: chebyshev1, Theorem 2.1 via `chebyshev1.Prefix.residualPolynomial_eq`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem residualPolynomial_eval (R : Realization ι) (n : ℕ) (lam : ℝ) :
    (R.residualPolynomial n).eval lam = R.scalarTransfer n lam := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  simp only [residualPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, scalarTransfer, scalarContract]
  have h := R.orderedProduct_polynomialStep_eval n lam
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← h]
  rfl

/--
Time-ordered two-spectral-variable kernel of Section 1.

Use: `chebyshev1.JacobiData.kernel_factorization` rewrites with this definition to
establish the identity stated in that declaration.

Article: chebyshev1, Theorem 2.2 via `chebyshev1.Prefix.kernel_zero`.
-/
def kernel (R : Realization ι) (n s : ℕ) (lam nu : ℝ) : ℝ :=
  -R.scalarContract
    (orderedProduct (fun i => R.scalarStep (s + 1 + i) lam) (n - (s + 1)) *
      R.queryFactor s * orderedProduct (fun i => R.scalarStep i nu) s)

variable [Fintype d] [DecidableEq d]

/--
`P_s ⊗ I - (g_s q_sᵀ) ⊗ H`, in coordinates on memory × physical space.

Use: `chebyshev1.Realization.operatorStep_add` rewrites with this definition to establish
exact identity `R.operatorStep s (H + E) = R.operatorStep s H + R.operatorInsertion s E`.

Article: chebyshev1, Theorem 2.1 via `chebyshev1.Prefix.operator_exact`.
-/
def operatorStep (R : Realization ι) (s : ℕ) (H : Matrix d d ℝ) :
    Matrix (ι × d) (ι × d) ℝ :=
  R.P s ⊗ₖ (1 : Matrix d d ℝ) - R.queryFactor s ⊗ₖ H

/--
The signed insertion caused by a Hessian perturbation.

Use: `chebyshev1.Realization.operatorInsertion_add` rewrites with this definition to
establish exact identity `R.operatorInsertion s (E + F) = R.operatorInsertion s E +
R.operatorInsertion s F`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.
-/
def operatorInsertion (R : Realization ι) (s : ℕ) (E : Matrix d d ℝ) :
    Matrix (ι × d) (ι × d) ℝ :=
  -(R.queryFactor s ⊗ₖ E)

omit [Fintype ι] [DecidableEq ι] [Fintype d] in
/--
Exact identity `R.operatorStep s (H + E) = R.operatorStep s H + R.operatorInsertion s E`.

Use: `chebyshev1.Realization.hasDerivAt_operatorTransfer` rewrites with this identity to
establish the actual derivative at the stated point: `HasDerivAt (fun δ : ℝ =>
R.operatorTransfer n (fun s => H + δ • B s)) (R.linearResponse n H B) 0`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem operatorStep_add (R : Realization ι) (s : ℕ) (H E : Matrix d d ℝ) :
    R.operatorStep s (H + E) = R.operatorStep s H + R.operatorInsertion s E := by
  simp only [operatorStep, operatorInsertion, Matrix.kronecker_add]
  abel

omit [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] in
/--
Exact identity `R.operatorInsertion s (E + F) = R.operatorInsertion s E + R.operatorInsertion s
F`.

Use: `chebyshev1.Realization.operatorInsertionLinear` uses this identity in the displayed
construction of `operatorInsertionLinear`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev1, Definition 1.2.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem operatorInsertion_add (R : Realization ι) (s : ℕ) (E F : Matrix d d ℝ) :
    R.operatorInsertion s (E + F) = R.operatorInsertion s E + R.operatorInsertion s F := by
  simp only [operatorInsertion, Matrix.kronecker_add]
  abel

omit [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] in
/--
Exact identity `R.operatorInsertion s (δ • E) = δ • R.operatorInsertion s E`.

Use: `chebyshev1.Realization.hasDerivAt_operatorTransfer` rewrites with this identity to
establish the actual derivative at the stated point: `HasDerivAt (fun δ : ℝ =>
R.operatorTransfer n (fun s => H + δ • B s)) (R.linearResponse n H B) 0`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem operatorInsertion_smul (R : Realization ι) (s : ℕ) (δ : ℝ) (E : Matrix d d ℝ) :
    R.operatorInsertion s (δ • E) = δ • R.operatorInsertion s E := by simp [operatorInsertion, Matrix.kronecker_smul]

/--
`(ℓᵀ ⊗ I) M (b ⊗ I)` without auxiliary singleton indices.

Use: `chebyshev1.Realization.contractLinear` uses this definition in the displayed
construction of `contractLinear`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev1, Theorem 2.1 via `chebyshev1.Prefix.operator_exact`.
-/
def contract (R : Realization ι) (M : Matrix (ι × d) (ι × d) ℝ) : Matrix d d ℝ :=
  fun x y => ∑ i, ∑ j, R.readout i * M (i, x) (j, y) * R.b j

/--
Input/output contraction is linear in the memory-space operator.

Use: `chebyshev1.Realization.contractLinear_apply` uses this definition to establish exact
identity `R.contractLinear M = R.contract M`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_driftRemainder_le`.
-/
def contractLinear (R : Realization ι) :
    Matrix (ι × d) (ι × d) ℝ →ₗ[ℝ] Matrix d d ℝ where
  toFun := R.contract
  map_add' M N := by
    ext x y
    simp [contract, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' c M := by
    ext x y
    simp [contract, Finset.mul_sum, mul_assoc, mul_left_comm]

omit [DecidableEq ι] [Fintype d] [DecidableEq d] in
/--
Exact identity `R.contractLinear M = R.contract M`.

Use: `chebyshev1.Realization.spectralPair_singleInsertion` rewrites with this identity to
establish the identity stated in that declaration.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
@[simp] theorem contractLinear_apply (R : Realization ι)
    (M : Matrix (ι × d) (ι × d) ℝ) : R.contractLinear M = R.contract M := rfl

/--
Defines `operatorTransfer` of type `Matrix d d ℝ` by `R.contract (orderedProduct (fun s =>
R.operatorStep s (H s)) n)`.

Use: `chebyshev1.JacobiData.driftOrder_zero` rewrites with this definition to establish
exact identity `J.driftOrder I N 0 H E = (J.realization I).operatorTransfer N (fun _ => H)`.

Article: chebyshev1, Theorem 2.1 via `chebyshev1.Prefix.operator_exact`.
-/
def operatorTransfer (R : Realization ι) (n : ℕ) (H : ℕ → Matrix d d ℝ) : Matrix d d ℝ :=
  R.contract (orderedProduct (fun s => R.operatorStep s (H s)) n)

end Realization
end
end chebyshev1
