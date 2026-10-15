import «2606.16671v2».TwoTerm.Quadratic
import Mathlib.Data.Matrix.Composition

/-!
Article: 2606.16671v2, Theorem 4.3.
Operator.
Use: `«2606.16671v2».TwoTerm.memoryProduct_aeval` feeds `«2606.16671v2».JacobiData.operator_tail`
(The operator tail fundamental solution; no commutativity of perturbations is assumed).
Proof chain: `«2606.16671v2».JacobiData.insertionTerm_blocks` — 2606.16671v2, Theorem 4.3; All
insertion orders, partition bounds, finite/cosh bounds and attainment.
-/
namespace «2606.16671v2»
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix BigOperators Kronecker

/--
Exact identity `f (orderedProduct C n) = orderedProduct (fun s => f (C s)) n`.

Use: `«2606.16671v2».TwoTerm.insertionTerm_eq_memory` uses this identity to establish the
identity stated in that declaration.

Article: 2606.16671v2, Corollary 5.4 via `«2606.16671v2».Nonlinear.lipschitzHessian_error_le`.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem orderedProduct_map {A B : Type*} [Monoid A] [Monoid B] (f : A →* B)
    (C : ℕ → A) (n : ℕ) : f (orderedProduct C n) = orderedProduct (fun s => f (C s)) n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [orderedProduct_succ, map_mul, ih]

namespace TwoTerm
variable (S : TwoTerm) {d : Type*} [Fintype d] [DecidableEq d]

/--
Defines `memoryStep` of type `Matrix (Fin 2) (Fin 2) (Matrix d d ℝ)` by `if s = 0 then !![1 -
S.gamma 0 • H, 0; 1, 0] else !![S.a s • (1 : Matrix d d ℝ) - S.gamma s • H, S.b s • (1 : Matrix
d d ℝ); 1, 0]`.

Use: `«2606.16671v2».TwoTerm.insertionTerm_eq_memory` uses this definition to establish the
identity stated in that declaration.

Article: 2606.16671v2, Corollary 5.4 via `«2606.16671v2».Nonlinear.lipschitzHessian_error_le`.
-/
def memoryStep (s : ℕ) (H : Matrix d d ℝ) : Matrix (Fin 2) (Fin 2) (Matrix d d ℝ) :=
  if s = 0 then !![1 - S.gamma 0 • H, 0; 1, 0]
  else !![S.a s • (1 : Matrix d d ℝ) - S.gamma s • H, S.b s • (1 : Matrix d d ℝ); 1, 0]

/--
Defines `memoryInsertion` of type `Matrix (Fin 2) (Fin 2) (Matrix d d ℝ)` by `!![-S.gamma s •
E, 0; 0, 0]`.

Use: `«2606.16671v2».TwoTerm.insertionTerm_eq_memory` uses this definition to establish the
identity stated in that declaration.

Article: 2606.16671v2, Corollary 5.3 via
`«2606.16671v2».SineJacobi.driftOrder_static_attained`.
-/
def memoryInsertion (s : ℕ) (E : Matrix d d ℝ) : Matrix (Fin 2) (Fin 2) (Matrix d d ℝ) :=
  !![-S.gamma s • E, 0; 0, 0]

/--
Exact identity `S.realization.operatorStep s H = Matrix.compRingEquiv (Fin 2) d ℝ (S.memoryStep
s H)`.

Use: `«2606.16671v2».TwoTerm.insertionTerm_eq_memory` rewrites with this identity to establish
the identity stated in that declaration.

Article: 2606.16671v2, Corollary 5.4 via `«2606.16671v2».Nonlinear.lipschitzHessian_error_le`.

Proof: Separate `s = 0` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Check each member of the finite index type; no case is omitted.
-/
theorem operatorStep_eq_memory (s : ℕ) (H : Matrix d d ℝ) :
    S.realization.operatorStep s H = Matrix.compRingEquiv (Fin 2) d ℝ (S.memoryStep s H) := by
  apply Matrix.ext
  rintro ⟨i, x⟩ ⟨j, y⟩
  fin_cases i <;> fin_cases j <;> by_cases hs : s = 0 <;>
    simp [Realization.operatorStep, Realization.queryFactor, realization, memoryStep,
      hs, Matrix.compRingEquiv_apply, Matrix.comp, Equiv.coe_fn_mk, Matrix.kroneckerMap_apply, Matrix.vecMulVec]

omit [DecidableEq d] in
/--
Exact identity `S.realization.operatorInsertion s E = Matrix.compRingEquiv (Fin 2) d ℝ
(S.memoryInsertion s E)`.

Use: `«2606.16671v2».TwoTerm.insertionTerm_eq_memory` rewrites with this identity to establish
the identity stated in that declaration.

Article: 2606.16671v2, Corollary 5.3 via
`«2606.16671v2».SineJacobi.driftOrder_static_attained`.

Proof: Check each member of the finite index type; no case is omitted.
-/
theorem operatorInsertion_eq_memory (s : ℕ) (E : Matrix d d ℝ) :
    S.realization.operatorInsertion s E =
      Matrix.compRingEquiv (Fin 2) d ℝ (S.memoryInsertion s E) := by
  apply Matrix.ext
  rintro ⟨i, x⟩ ⟨j, y⟩
  fin_cases i <;> fin_cases j <;>
    simp [Realization.operatorInsertion, Realization.queryFactor, realization, memoryInsertion,
      Matrix.compRingEquiv_apply, Matrix.comp, Equiv.coe_fn_mk, Matrix.kroneckerMap_apply, Matrix.vecMulVec]

omit [DecidableEq d] in
/--
Exact identity `S.realization.contract (Matrix.compRingEquiv (Fin 2) d ℝ M) = M 0 0`.

Use: `«2606.16671v2».TwoTerm.insertionTerm_eq_memory` uses this identity to establish the
identity stated in that declaration.

Article: 2606.16671v2, Corollary 5.4 via `«2606.16671v2».Nonlinear.lipschitzHessian_error_le`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem contract_memory (M : Matrix (Fin 2) (Fin 2) (Matrix d d ℝ)) :
    S.realization.contract (Matrix.compRingEquiv (Fin 2) d ℝ M) = M 0 0 := by
  apply Matrix.ext
  intro x y
  simp [Realization.contract, realization, Fin.sum_univ_two, Matrix.compRingEquiv_apply, Matrix.comp, Equiv.coe_fn_mk]

/--
Exact identity `S.realization.operatorTransfer N Hs = orderedProduct (fun s => S.memoryStep s
(Hs s)) N 0 0`.

Use: `«2606.16671v2».JacobiData.operator_prefix` rewrites with this identity to establish exact
identity `orderedProduct (fun s => (J.method I).memoryStep s H) n 0 0 = (J.den I n)⁻¹ • aeval H
(J.spectralBlock I 0 n)`.

Article: 2606.16671v2, Corollary 5.4 via `«2606.16671v2».Nonlinear.lipschitzHessian_error_le`.

Proof: Use the identities/estimates `«2606.16671v2».TwoTerm.operatorStep_eq_memory`,
`«2606.16671v2».orderedProduct_map`, `«2606.16671v2».TwoTerm.contract_memory` with the
arguments shown in the proof.
-/
theorem operatorTransfer_eq_memory (N : ℕ) (Hs : ℕ → Matrix d d ℝ) :
    S.realization.operatorTransfer N Hs = orderedProduct (fun s => S.memoryStep s (Hs s)) N 0 0 := by
  unfold Realization.operatorTransfer
  simp_rw [operatorStep_eq_memory]
  have h := orderedProduct_map (Matrix.compRingEquiv (Fin 2) d ℝ).toMonoidHom
    (fun s => S.memoryStep s (Hs s)) N
  exact (congrArg S.realization.contract h).symm.trans (S.contract_memory _)

/--
Exact identity `S.realization.contract (insertionTerm (fun s => S.realization.operatorStep s H)
(fun s => S.realization.operatorInsertion s (E s)) N times) = insertionTerm (fun s =>
S.memoryStep s H) (fun s => S.memoryInsertion s (E s)) N times 0 0`.

Use: `«2606.16671v2».JacobiData.insertionTerm_blocks` rewrites with this identity to establish
the identity stated in that declaration.

Article: 2606.16671v2, Corollary 5.3 via
`«2606.16671v2».SineJacobi.driftOrder_static_attained`.

Proof: Use the identities/estimates `«2606.16671v2».TwoTerm.operatorStep_eq_memory`,
`«2606.16671v2».TwoTerm.operatorInsertion_eq_memory`, `«2606.16671v2».orderedProduct_map` with
the arguments shown in the proof.
-/
theorem insertionTerm_eq_memory (N : ℕ) (H : Matrix d d ℝ) (E : ℕ → Matrix d d ℝ)
    (times : Finset ℕ) :
    S.realization.contract (insertionTerm (fun s => S.realization.operatorStep s H)
      (fun s => S.realization.operatorInsertion s (E s)) N times) =
      insertionTerm (fun s => S.memoryStep s H) (fun s => S.memoryInsertion s (E s)) N times 0 0 := by
  -- Use the identities/estimates `«2606.16671v2».TwoTerm.operatorStep_eq_memory`,
  -- `«2606.16671v2».TwoTerm.operatorInsertion_eq_memory`, `«2606.16671v2».orderedProduct_map`
  -- with the arguments shown in the proof.
  unfold insertionTerm
  simp_rw [operatorStep_eq_memory, operatorInsertion_eq_memory]
  have hi (s : ℕ) :
      (if s ∈ times then Matrix.compRingEquiv (Fin 2) d ℝ (S.memoryInsertion s (E s))
        else Matrix.compRingEquiv (Fin 2) d ℝ (S.memoryStep s H)) =
      Matrix.compRingEquiv (Fin 2) d ℝ (if s ∈ times then S.memoryInsertion s (E s) else S.memoryStep s H) := by
    split_ifs <;> rfl
  simp_rw [hi]
  have h := orderedProduct_map (Matrix.compRingEquiv (Fin 2) d ℝ).toMonoidHom
    (fun i => if i ∈ times then S.memoryInsertion i (E i) else S.memoryStep i H) N
  exact (congrArg S.realization.contract h).symm.trans (S.contract_memory _)

/--
Exact identity `S.memoryStep s H i j = Polynomial.aeval H (S.realization.polynomialStep s i
j)`.

Use: `«2606.16671v2».TwoTerm.memoryProduct_aeval` rewrites with this identity to establish
exact identity `orderedProduct (fun s => S.memoryStep (a + s) H) n i j = Polynomial.aeval H
(orderedProduct (fun s => S.realization.polynomialStep (a + s)) n i j)`.

Article: 2606.16671v2, Corollary 5.3 via
`«2606.16671v2».SineJacobi.driftOrder_static_attained`.

Proof: Use the identities/estimates `«2606.16671v2».Realization.polynomialStep_aeval`,
`«2606.16671v2».TwoTerm.operatorStep_eq_memory` with the arguments shown in the proof.
-/
theorem memoryStep_aeval (s : ℕ) (H : Matrix d d ℝ) (i j : Fin 2) :
    S.memoryStep s H i j = Polynomial.aeval H (S.realization.polynomialStep s i j) := by
  apply Matrix.ext
  intro x y
  rw [Realization.polynomialStep_aeval, operatorStep_eq_memory]
  rfl

/--
Exact identity `orderedProduct (fun s => S.memoryStep (a + s) H) n i j = Polynomial.aeval H
(orderedProduct (fun s => S.realization.polynomialStep (a + s)) n i j)`.

Use: `«2606.16671v2».JacobiData.operator_tail` rewrites with this identity to establish exact
identity `orderedProduct (fun s => (J.method I).memoryStep (r + s) H) (N - r) 0 0 = (J.den I r
/ J.den I N) • aeval H (J.spectralBlock I r (N - r))`.

Article: 2606.16671v2, Corollary 5.3 via
`«2606.16671v2».SineJacobi.driftOrder_static_attained`.

Proof: Induct on `n` while keeping `i j` arbitrary; the recursive step uses the
previous-stage assertion. Separate `i = j` from its negation; prove the goal under each of
these mutually exclusive hypotheses.
-/
theorem memoryProduct_aeval (a n : ℕ) (H : Matrix d d ℝ) (i j : Fin 2) :
    orderedProduct (fun s => S.memoryStep (a + s) H) n i j =
      Polynomial.aeval H (orderedProduct (fun s => S.realization.polynomialStep (a + s)) n i j) := by
  induction n generalizing i j with
  | zero => by_cases hij : i = j <;> simp [hij]
  | succ n ih =>
    simp only [orderedProduct_succ, Matrix.mul_apply, map_sum, map_mul, ih, memoryStep_aeval]

end TwoTerm
end
end «2606.16671v2»
