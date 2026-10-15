import «2606.16671v2».Jacobi.Determinant
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Logic.Equiv.Fin.Basic

/-!
Article: 2606.16671v2, Theorem 5.2.
Cramer's rule for every diagonal entry of a Jacobi resolvent.
Use: `«2606.16671v2».JacobiData.resolvent_diagonal` feeds `«2610.05164v2».Jacobi.green_diagonal`
(green diagonal).
Proof chain: `«2606.16671v2».SineJacobi.gain_exact_resolvent` — 2606.16671v2, Theorem 5.2; Exact
sine gain, resolvent expression, asymptotics and energy value.
-/
namespace «2606.16671v2».JacobiData
noncomputable section
open Polynomial
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
variable (J : JacobiData)

/--
Defines `splitIndex` of type `Fin s.val ⊕ Fin (n-s.val) ≃ Fin n` by `finSumFinEquiv.trans
(finCongr (by omega))`.

Use: `«2606.16671v2».JacobiData.shifted_minor_det` uses this definition to establish exact
identity `((Matrix.scalar (Fin (n+1)) x-J.matrix 0 (n+1)).submatrix s.succAbove
s.succAbove).det = (J.leading s.val).eval x*(J.block (s.val+1) (n-s.val)).eval x`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.gain_exact_resolvent`.
-/
def splitIndex (n : ℕ) (s : Fin (n+1)) : Fin s.val ⊕ Fin (n-s.val) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (by omega))

/--
Exact identity `(splitIndex n s (Sum.inl i)).val = i.val`.

Use: `«2606.16671v2».JacobiData.skip_split_left` uses this identity to establish the identity
`(s.succAbove (splitIndex n s (Sum.inl i))).val = i.val`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.gain_exact_resolvent`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[simp] theorem splitIndex_left (n : ℕ) (s : Fin (n+1)) (i : Fin s.val) :
    (splitIndex n s (Sum.inl i)).val = i.val := by simp [splitIndex]

/--
Exact identity `(splitIndex n s (Sum.inr i)).val = s.val+i.val`.

Use: `«2606.16671v2».JacobiData.skip_split_right` uses this identity to establish exact
identity `(s.succAbove (splitIndex n s (Sum.inr i))).val = s.val+1+i.val`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.gain_exact_resolvent`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[simp] theorem splitIndex_right (n : ℕ) (s : Fin (n+1)) (i : Fin (n-s.val)) :
    (splitIndex n s (Sum.inr i)).val = s.val+i.val := by simp [splitIndex]

/--
Exact identity `(s.succAbove (splitIndex n s (Sum.inl i))).val = i.val`.

Use: `«2606.16671v2».JacobiData.shifted_minor_split` rewrites with this identity to establish
the identity stated in that declaration.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.gain_exact_resolvent`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
@[simp] theorem skip_split_left (n : ℕ) (s : Fin (n+1)) (i : Fin s.val) :
    (s.succAbove (splitIndex n s (Sum.inl i))).val = i.val := by simp [Fin.succAbove, Fin.lt_def, i.isLt]

/--
Exact identity `(s.succAbove (splitIndex n s (Sum.inr i))).val = s.val+1+i.val`.

Use: `«2606.16671v2».JacobiData.shifted_minor_split` rewrites with this identity to establish
the identity stated in that declaration.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.gain_exact_resolvent`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
@[simp] theorem skip_split_right (n : ℕ) (s : Fin (n+1)) (i : Fin (n-s.val)) :
    (s.succAbove (splitIndex n s (Sum.inr i))).val = s.val+1+i.val := by
  simp [Fin.succAbove, Fin.lt_def, show ¬s.val+i.val < s.val by omega]
  omega

/--
Exact identity `(Matrix.scalar (Fin n) x-J.matrix a n) i j = if i = j then x-J.b (a+i.val) else
if i.val+1 = j.val then -Real.sqrt (J.aSq (a+j.val)) else if j.val+1 = i.val then -Real.sqrt
(J.aSq (a+i.val)) else 0`.

Use: `«2606.16671v2».JacobiData.shifted_minor_split` rewrites with this identity to establish
the identity stated in that declaration.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.gain_exact_resolvent`.

Proof: Separate `i = j` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem shifted_apply (a n : ℕ) (x : ℝ) (i j : Fin n) :
    (Matrix.scalar (Fin n) x-J.matrix a n) i j =
      if i = j then x-J.b (a+i.val)
      else if i.val+1 = j.val then -Real.sqrt (J.aSq (a+j.val))
      else if j.val+1 = i.val then -Real.sqrt (J.aSq (a+i.val)) else 0 := by
  -- Separate `i = j` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  simp only [Matrix.sub_apply, J.matrix_apply]
  by_cases hij : i = j
  · subst j
    simp [Matrix.scalar, Pi.algebraMap_def]
  · simp [Matrix.scalar, Pi.algebraMap_def, hij]
    split_ifs <;> simp


/--
Deleting a site disconnects its two adjacent principal blocks.

Use: `«2606.16671v2».JacobiData.shifted_minor_det` rewrites with this identity to establish
exact identity `((Matrix.scalar (Fin (n+1)) x-J.matrix 0 (n+1)).submatrix s.succAbove
s.succAbove).det = (J.leading s.val).eval x*(J.block (s.val+1) (n-s.val)).eval x`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.gain_exact_resolvent`.

Proof: Use the identities/estimates `«2606.16671v2».JacobiData.shifted_apply`,
`«2606.16671v2».JacobiData.skip_split_left`, `«2606.16671v2».JacobiData.skip_split_right` with
the arguments shown in the proof.
-/
theorem shifted_minor_split (n : ℕ) (s : Fin (n+1)) (x : ℝ) :
    (Matrix.scalar (Fin (n+1)) x-J.matrix 0 (n+1)).submatrix
      (fun i => s.succAbove (splitIndex n s i)) (fun i => s.succAbove (splitIndex n s i)) =
      Matrix.fromBlocks (Matrix.scalar (Fin s.val) x-J.matrix 0 s.val) 0 0
        (Matrix.scalar (Fin (n-s.val)) x-J.matrix (s.val+1) (n-s.val)) := by
  -- Use the identities/estimates `«2606.16671v2».JacobiData.shifted_apply`,
  -- `«2606.16671v2».JacobiData.skip_split_left`, `«2606.16671v2».JacobiData.skip_split_right`
  -- with the arguments shown in the proof.
  apply Matrix.ext
  intro i j
  cases i <;> cases j <;>
    simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, J.shifted_apply, Fin.ext_iff,
      skip_split_left, skip_split_right, Nat.zero_add, Matrix.zero_apply]
  all_goals split_ifs <;> first | omega | rfl


/--
Exact identity `((Matrix.scalar (Fin (n+1)) x-J.matrix 0 (n+1)).submatrix s.succAbove
s.succAbove).det = (J.leading s.val).eval x*(J.block (s.val+1) (n-s.val)).eval x`.

Use: `«2606.16671v2».JacobiData.resolvent_diagonal` rewrites with this identity to establish
exact identity `(Matrix.scalar (Fin (n+1)) x-J.matrix 0 (n+1))⁻¹ s s = (J.leading s.val).eval
x*(J.block (s.val+1) (n-s.val)).eval x / (J.leading (n+1)).eval x`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.gain_exact_resolvent`.

Proof: Use the identities/estimates `«2606.16671v2».JacobiData.block_eq_charpoly`,
`«2606.16671v2».JacobiData.shifted_minor_split` with the arguments shown in the proof.
-/
theorem shifted_minor_det (n : ℕ) (s : Fin (n+1)) (x : ℝ)
    (hsq : ∀ t, 0 ≤ J.aSq t) :
    ((Matrix.scalar (Fin (n+1)) x-J.matrix 0 (n+1)).submatrix s.succAbove s.succAbove).det =
      (J.leading s.val).eval x*(J.block (s.val+1) (n-s.val)).eval x := by
  -- Use the identities/estimates `«2606.16671v2».JacobiData.block_eq_charpoly`,
  -- `«2606.16671v2».JacobiData.shifted_minor_split` with the arguments shown in the proof.
  have hd := Matrix.det_submatrix_equiv_self (splitIndex n s)
    ((Matrix.scalar (Fin (n+1)) x-J.matrix 0 (n+1)).submatrix s.succAbove s.succAbove)
  rw [Matrix.submatrix_submatrix] at hd
  simp only [Function.comp_def] at hd
  rw [J.shifted_minor_split n s x, Matrix.det_fromBlocks_zero₂₁] at hd
  rw [← Matrix.eval_charpoly, ← Matrix.eval_charpoly,
    ← J.block_eq_charpoly hsq, ← J.block_eq_charpoly hsq] at hd
  exact hd.symm

/--
Cramer's rule for every diagonal entry of a Jacobi resolvent.

Exact identity `(Matrix.scalar (Fin (n+1)) x-J.matrix 0 (n+1))⁻¹ s s = (J.leading s.val).eval
x*(J.block (s.val+1) (n-s.val)).eval x / (J.leading (n+1)).eval x`.

Use: `«2606.16671v2».SineJacobi.resolvent_diagonal` uses this identity to establish exact
identity `(1-(data N).matrix 0 N)⁻¹ s s = greenWeight N s.val`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.gain_exact_resolvent`.

Proof: Use the identities/estimates `«2606.16671v2».JacobiData.shifted_minor_det`,
`«2606.16671v2».JacobiData.block_eq_charpoly` with the arguments shown in the proof.
-/
theorem resolvent_diagonal (n : ℕ) (s : Fin (n+1)) (x : ℝ)
    (hsq : ∀ t, 0 ≤ J.aSq t) :
    (Matrix.scalar (Fin (n+1)) x-J.matrix 0 (n+1))⁻¹ s s =
      (J.leading s.val).eval x*(J.block (s.val+1) (n-s.val)).eval x /
        (J.leading (n+1)).eval x := by
  -- Use the identities/estimates `«2606.16671v2».JacobiData.shifted_minor_det`,
  -- `«2606.16671v2».JacobiData.block_eq_charpoly` with the arguments shown in the proof.
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_fin_succ_eq_det_submatrix,
    show s.val+s.val = 2*s.val by omega, pow_mul, neg_one_sq, one_pow, one_mul,
    J.shifted_minor_det n s x hsq, ← Matrix.eval_charpoly, ← J.block_eq_charpoly hsq]
  simp only [Ring.inverse_eq_inv, div_eq_mul_inv, JacobiData.leading]
  ring

end
end «2606.16671v2».JacobiData
