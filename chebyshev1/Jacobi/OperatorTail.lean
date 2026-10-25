import chebyshev1.Jacobi.Kernel
import chebyshev1.TwoTerm.Operator

/-!
Article: chebyshev1, Theorem 4.3.
The operator tail fundamental solution; no commutativity of perturbations is assumed.
Use: `chebyshev1.JacobiData.operator_prefix` feeds
`chebyshev1.JacobiData.insertionTerm_blocks` (Each time-ordered insertion has exactly the
adjacent continuant blocks of 4.3(i)).
Proof chain: `chebyshev1.JacobiData.insertionTerm_blocks` — chebyshev1, Theorem 4.3; All
insertion orders, partition bounds, finite/cosh bounds and attainment.
-/
namespace chebyshev1.JacobiData
noncomputable section
open Polynomial
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false
variable (J : JacobiData) (I : SpectralInterval)

/--
Exact identity `(orderedProduct (fun s => (J.realization I).polynomialStep (r + s)) n).map
(eval lam) = orderedProduct (fun s => (J.realization I).scalarStep (r + s) lam) n`.

Use: `chebyshev1.JacobiData.polynomial_tail` uses this identity to establish the identity
`orderedProduct (fun s => (J.realization I).polynomialStep (r + s)) (N - r) 0 0 = C (J.den I r
/ J.den I N) * J.spectralBlock I r (N - r)`.

Article: chebyshev1, Corollary 5.3 via
`chebyshev1.SineJacobi.driftOrder_static_attained`.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion. Separate `i = j`
from its negation; prove the goal under each of these mutually exclusive hypotheses.
-/
theorem polynomialTail_eval (r n : ℕ) (lam : ℝ) :
    (orderedProduct (fun s => (J.realization I).polynomialStep (r + s)) n).map (eval lam) =
      orderedProduct (fun s => (J.realization I).scalarStep (r + s) lam) n := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  induction n with
  | zero => ext i j; by_cases hij : i = j <;> simp [hij]
  | succ n ih =>
    rw [orderedProduct_succ, orderedProduct_succ]
    rw [show ((J.realization I).polynomialStep (r + n) *
      orderedProduct (fun s => (J.realization I).polynomialStep (r + s)) n).map (eval lam) =
      ((J.realization I).polynomialStep (r + n)).map (eval lam) *
      (orderedProduct (fun s => (J.realization I).polynomialStep (r + s)) n).map (eval lam) from
      Matrix.map_mul (f := evalRingHom lam)]
    rw [Realization.polynomialStep_eval, ih]

/--
Exact identity `orderedProduct (fun s => (J.realization I).polynomialStep (r + s)) (N - r) 0 0
= C (J.den I r / J.den I N) * J.spectralBlock I r (N - r)`.

Use: `chebyshev1.JacobiData.operator_tail` rewrites with this identity to establish exact
identity `orderedProduct (fun s => (J.method I).memoryStep (r + s) H) (N - r) 0 0 = (J.den I r
/ J.den I N) • aeval H (J.spectralBlock I r (N - r))`.

Article: chebyshev1, Corollary 5.3 via
`chebyshev1.SineJacobi.driftOrder_static_attained`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem polynomial_tail {N : ℕ} (h : J.Admissible I N) (r : ℕ)
    (hr : 1 ≤ r) (hrN : r ≤ N) :
    orderedProduct (fun s => (J.realization I).polynomialStep (r + s)) (N - r) 0 0 =
      C (J.den I r / J.den I N) * J.spectralBlock I r (N - r) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  apply Polynomial.funext
  intro lam
  have hp := congrArg (fun M => M 0 0) (J.polynomialTail_eval I r (N - r) lam)
  change (orderedProduct (fun s => (J.realization I).polynomialStep (r + s)) (N - r) 0 0).eval lam =
    orderedProduct (fun s => (J.realization I).scalarStep (r + s) lam) (N - r) 0 0 at hp
  rw [hp, J.tail_fundamental I h r hr hrN]
  simp [spectralBlock_eval]

/--
The operator tail fundamental solution; no commutativity of perturbations is assumed.

Exact identity `orderedProduct (fun s => (J.method I).memoryStep (r + s) H) (N - r) 0 0 =
(J.den I r / J.den I N) • aeval H (J.spectralBlock I r (N - r))`.

Use: `chebyshev1.JacobiData.insertionTerm_blocks` rewrites with this identity to establish
the identity stated in that declaration.

Article: chebyshev1, Corollary 5.3 via
`chebyshev1.SineJacobi.driftOrder_static_attained`.

Proof: Use the identities/estimates `chebyshev1.TwoTerm.memoryProduct_aeval`,
`chebyshev1.JacobiData.polynomial_tail` with the arguments shown in the proof.
-/
theorem operator_tail {d : Type*} [Fintype d] [DecidableEq d] {N : ℕ}
    (h : J.Admissible I N) (r : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N) (H : Matrix d d ℝ) :
    orderedProduct (fun s => (J.method I).memoryStep (r + s) H) (N - r) 0 0 =
      (J.den I r / J.den I N) • aeval H (J.spectralBlock I r (N - r)) := by
  -- Use the identities/estimates `chebyshev1.TwoTerm.memoryProduct_aeval`,
  -- `chebyshev1.JacobiData.polynomial_tail` with the arguments shown in the proof.
  rw [TwoTerm.memoryProduct_aeval]
  change aeval H (orderedProduct (fun s => (J.realization I).polynomialStep (r + s)) (N - r) 0 0) = _
  rw [J.polynomial_tail I h r hr hrN, map_mul, aeval_C,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

/--
Exact identity `orderedProduct (fun s => (J.method I).memoryStep s H) n 0 0 = (J.den I n)⁻¹ •
aeval H (J.spectralBlock I 0 n)`.

Use: `chebyshev1.JacobiData.insertionTerm_blocks` uses this identity to establish the
identity stated in that declaration.

Article: chebyshev1, Corollary 5.3 via
`chebyshev1.SineJacobi.driftOrder_static_attained`.

Proof: Use the identities/estimates `chebyshev1.TwoTerm.operatorTransfer_eq_memory`,
`chebyshev1.JacobiData.operator_exact` with the arguments shown in the proof.
-/
theorem operator_prefix {d : Type*} [Fintype d] [DecidableEq d] {N : ℕ}
    (h : J.Admissible I N) (n : ℕ) (hn : n ≤ N) (H : Matrix d d ℝ) :
    orderedProduct (fun s => (J.method I).memoryStep s H) n 0 0 =
      (J.den I n)⁻¹ • aeval H (J.spectralBlock I 0 n) := by
  -- Use the identities/estimates `chebyshev1.TwoTerm.operatorTransfer_eq_memory`,
  -- `chebyshev1.JacobiData.operator_exact` with the arguments shown in the proof.
  rw [← TwoTerm.operatorTransfer_eq_memory]
  change (J.realization I).operatorTransfer n (fun _ => H) = _
  rw [J.operator_exact I h n hn]
  simp only [residual, leading, spectralBlock, map_mul, aeval_C,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

end
end chebyshev1.JacobiData
