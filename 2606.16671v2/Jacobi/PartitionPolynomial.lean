import «2606.16671v2».Jacobi.DriftOrders
import «2606.16671v2».Jacobi.EndpointBound
import Mathlib.Algebra.Polynomial.Taylor

/-!
Article: 2606.16671v2, Theorem 4.3.
The insertion coefficients are exactly the Taylor coefficients of the terminal continuant.
Use: `«2606.16671v2».JacobiData.taylor_leading_coeff` feeds
`«2606.16671v2».JacobiData.driftOrder_static_value` (Every homogeneous insertion order attains its
endpoint partition constant).
Proof chain: `«2606.16671v2».JacobiData.opNorm_driftOrder_static` — 2606.16671v2, Theorem 4.3; All
insertion orders, partition bounds, finite/cosh bounds and attainment.
-/
namespace «2606.16671v2»
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/--
Exact identity `scalarMatrix a * scalarMatrix b = scalarMatrix (a*b)`.

Use: `«2606.16671v2».blockWord_scalarMatrix` rewrites with this identity to establish exact
identity `blockWord (fun a k => scalarMatrix (B a k)) (fun _ => scalarMatrix e) n times =
scalarMatrix (e^times.length * blockWord B (fun _ => 1) n times)`.

Article: 2606.16671v2, Corollary 5.3 via
`«2606.16671v2».SineJacobi.driftOrder_static_attained`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem scalarMatrix_mul (a b : ℝ) : scalarMatrix a * scalarMatrix b = scalarMatrix (a*b) := by simp [scalarMatrix, Matrix.diagonal_mul_diagonal]

/--
Exact identity `scalarMatrix a + scalarMatrix b = scalarMatrix (a+b)`.

Use: `«2606.16671v2».JacobiData.taylor_leading_partition` rewrites with this identity to
establish exact identity `taylor 1 (J.leading N) = ∑ times ∈ (Finset.range N).powerset, C
(J.endpointWeight N times) * X^times.card`.

Article: 2606.16671v2, Corollary 5.3 via
`«2606.16671v2».SineJacobi.driftOrder_static_attained`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem scalarMatrix_add (a b : ℝ) : scalarMatrix a + scalarMatrix b = scalarMatrix (a+b) := by simp [scalarMatrix, Matrix.diagonal_add]

/--
Exact identity `a • scalarMatrix b = scalarMatrix (a*b)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2606.16671v2, Theorem 4.3.

Proof: Check each member of the finite index type; no case is omitted.
-/
theorem scalarMatrix_smul (a b : ℝ) : a • scalarMatrix b = scalarMatrix (a*b) := by
  ext i j
  fin_cases i; fin_cases j
  rfl

/--
Exact identity `blockWord (fun a k => scalarMatrix (B a k)) (fun _ => scalarMatrix e) n times =
scalarMatrix (e^times.length * blockWord B (fun _ => 1) n times)`.

Use: `«2606.16671v2».JacobiData.operatorWord_static` rewrites with this identity to establish
exact identity `J.operatorWord I (scalarMatrix I.mu) (fun _ => scalarMatrix e) n times =
scalarMatrix (e^times.card * J.endpointWeight n times)`.

Article: 2606.16671v2, Corollary 5.3 via
`«2606.16671v2».SineJacobi.driftOrder_static_attained`.

Proof: Induct on `times` while keeping `n` arbitrary; the recursive step uses the
previous-stage assertion.
-/
theorem blockWord_scalarMatrix (B : ℕ → ℕ → ℝ) (e : ℝ) (n : ℕ) (times : List ℕ) :
    blockWord (fun a k => scalarMatrix (B a k)) (fun _ => scalarMatrix e) n times =
      scalarMatrix (e^times.length * blockWord B (fun _ => 1) n times) := by
  -- Induct on `times` while keeping `n` arbitrary; the recursive step uses the
  -- previous-stage assertion.
  induction times generalizing n with
  | nil => simp [blockWord]
  | cons s times ih =>
    simp only [blockWord, ih, scalarMatrix_mul, List.length_cons, pow_succ, mul_one]
    congr 1
    ring

namespace JacobiData
variable (J : JacobiData) (I : SpectralInterval)

/--
Defines `endpointWeight` of type `ℝ` by `blockWord (fun a k => (J.block a k).eval 1) (fun _ =>
1) n (times.sort (· ≥ ·))`.

Use: `«2606.16671v2».JacobiData.operatorWord_static` uses this definition to establish exact
identity `J.operatorWord I (scalarMatrix I.mu) (fun _ => scalarMatrix e) n times = scalarMatrix
(e^times.card * J.endpointWeight n times)`.

Article: 2606.16671v2, Corollary 5.3 via
`«2606.16671v2».SineJacobi.driftOrder_static_attained`.
-/
def endpointWeight (n : ℕ) (times : Finset ℕ) : ℝ :=
  blockWord (fun a k => (J.block a k).eval 1) (fun _ => 1) n (times.sort (· ≥ ·))

/--
Exact identity `J.operatorWord I (scalarMatrix I.mu) (fun _ => scalarMatrix e) n times =
scalarMatrix (e^times.card * J.endpointWeight n times)`.

Use: `«2606.16671v2».JacobiData.taylor_leading_partition` rewrites with this identity to
establish exact identity `taylor 1 (J.leading N) = ∑ times ∈ (Finset.range N).powerset, C
(J.endpointWeight N times) * X^times.card`.

Article: 2606.16671v2, Corollary 5.3 via
`«2606.16671v2».SineJacobi.driftOrder_static_attained`.

Proof: Use the identities/estimates `«2606.16671v2».aeval_diagonal`,
`«2606.16671v2».JacobiData.spectralBlock_eval`, `«2606.16671v2».SpectralInterval.z_mu` with the
arguments shown in the proof.
-/
theorem operatorWord_static (e : ℝ) (n : ℕ) (times : Finset ℕ) :
    J.operatorWord I (scalarMatrix I.mu) (fun _ => scalarMatrix e) n times =
      scalarMatrix (e^times.card * J.endpointWeight n times) := by
  unfold operatorWord endpointWeight
  have he (a k : ℕ) : aeval (scalarMatrix I.mu) (J.spectralBlock I a k) =
      scalarMatrix ((J.block a k).eval 1) := by
    simp only [scalarMatrix, aeval_diagonal, spectralBlock_eval, I.z_mu]
  simp only [he, blockWord_scalarMatrix, Finset.length_sort]

/--
The insertion coefficients are exactly the Taylor coefficients of the terminal continuant.

Exact identity `taylor 1 (J.leading N) = ∑ times ∈ (Finset.range N).powerset, C
(J.endpointWeight N times) * X^times.card`.

Use: `«2606.16671v2».JacobiData.taylor_leading_coeff` rewrites with this identity to establish
exact identity `(taylor 1 (J.leading N)).coeff k = ∑ times ∈ (Finset.range N).powersetCard k,
J.endpointWeight N times`.

Article: 2606.16671v2, Corollary 5.3 via
`«2606.16671v2».SineJacobi.driftOrder_static_attained`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem taylor_leading_partition {N : ℕ} (h : J.Admissible I N) :
    taylor 1 (J.leading N) =
      ∑ times ∈ (Finset.range N).powerset, C (J.endpointWeight N times) * X^times.card := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  apply Polynomial.funext
  intro u
  let e : ℝ := -(I.delta/2*u)
  have hf := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℝ => M 0 0)
    (J.finiteDrift_words I h (scalarMatrix I.mu) (fun _ => scalarMatrix e))
  simp only [scalarMatrix_add] at hf
  rw [J.operator_exact I h N le_rfl] at hf
  simp only [J.operatorWord_static I] at hf
  simp only [scalarMatrix, aeval_diagonal, Matrix.diagonal_apply_eq,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at hf
  have hz : I.z (I.mu + e) = 1+u := by
    rw [I.z_eq, mul_add]
    have hmu := I.z_mu
    rw [I.z_eq] at hmu
    dsimp [e]
    rw [show I.eta - (2 / I.delta * I.mu + 2 / I.delta * -(I.delta / 2 * u)) =
      (I.eta - 2 / I.delta * I.mu) - 2 / I.delta * -(I.delta / 2 * u) by ring, hmu]
    field_simp [ne_of_gt I.delta_pos]
    ring
  rw [J.residual_eval I, hz] at hf
  have term (times : Finset ℕ) : (-(2/I.delta))^times.card / J.den I N *
      (e^times.card * J.endpointWeight N times) =
      (J.endpointWeight N times * u^times.card) / J.den I N := by
    dsimp [e]
    have hh : -(2 / I.delta) * -(I.delta / 2 * u) = u := by
      field_simp [ne_of_gt I.delta_pos]
    calc
      _ = ((-(2/I.delta) * -(I.delta/2*u))^times.card * J.endpointWeight N times) / J.den I N := by
        rw [mul_pow]; ring
      _ = _ := by rw [hh]; ring
  simp only [term] at hf
  rw [← Finset.sum_div] at hf
  have hf' := (div_left_inj' (J.den_ne I h le_rfl)).mp hf
  simpa only [taylor_eval, add_comm u 1, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X] using hf'

/--
Exact identity `(taylor 1 (J.leading N)).coeff k = ∑ times ∈ (Finset.range N).powersetCard k,
J.endpointWeight N times`.

Use: `«2606.16671v2».JacobiData.driftOrder_static_value` rewrites with this identity to
establish exact identity `J.driftOrder I N k (scalarMatrix I.mu) (fun _ => scalarMatrix
(-delta)) = scalarMatrix ((2*delta/I.delta)^k/J.den I N*(taylor 1 (J.leading N)).coeff k)`.

Article: 2606.16671v2, Corollary 5.3 via
`«2606.16671v2».SineJacobi.driftOrder_static_attained`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem taylor_leading_coeff {N : ℕ} (h : J.Admissible I N) (k : ℕ) :
    (taylor 1 (J.leading N)).coeff k =
      ∑ times ∈ (Finset.range N).powersetCard k, J.endpointWeight N times := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  rw [J.taylor_leading_partition I h]
  simp only [finsetSum_coeff, coeff_C_mul_X_pow]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext times
    simp [Finset.mem_powersetCard, Finset.mem_powerset, eq_comm]
  · intro times ht
    simp

end JacobiData
end
end «2606.16671v2»
