import «2610.05164v2».Green.Rows
import «2606.16671v2».Jacobi.ContinuantIdentities

/-!
Article: 2610.05164v2, Proposition 1.
Elimination of all rows preceding a site, directly from the true inverse.
Use: `«2610.05164v2».Jacobi.green_forward` feeds `«2610.05164v2».Jacobi.green_markov` (green
markov).
Proof chain: `«2610.05164v2».Packing.exists_representation` — 2610.05164v2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
-/
namespace «2610.05164v2».Jacobi
noncomputable section
open «2606.16671v2» Polynomial Matrix
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} (J : Jacobi N)

/--
Defines `prefixMinor` of type `(n : ℕ)` by `(J.data.leading n).eval 1`.

Use: `«2610.05164v2».Jacobi.forwardRatio` uses this definition in the displayed construction of
`forwardRatio`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.exists_representation`.
-/
def prefixMinor (n : ℕ) := (J.data.leading n).eval 1
/--
Exact identity `J.prefixMinor 0 = 1`.

Use: `«2610.05164v2».Jacobi.green_forward_identity` uses this identity to establish exact
identity `J.prefixMinor (n+1)*J.green ⟨n,by omega⟩ j = Real.sqrt (J.data.aSq
(n+1))*J.prefixMinor n*J.green ⟨n+1,hn⟩ j`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.exists_representation`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[simp] theorem prefixMinor_zero : J.prefixMinor 0 = 1 := by simp [prefixMinor]
/--
Exact identity `J.prefixMinor 1 = 1-J.data.b 0`.

Use: `«2610.05164v2».Jacobi.green_forward_identity` uses this identity to establish exact
identity `J.prefixMinor (n+1)*J.green ⟨n,by omega⟩ j = Real.sqrt (J.data.aSq
(n+1))*J.prefixMinor n*J.green ⟨n+1,hn⟩ j`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.exists_representation`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem prefixMinor_one : J.prefixMinor 1 = 1-J.data.b 0 := by simp [prefixMinor]
/--
Exact identity `J.prefixMinor (n+2) = (1-J.data.b (n+1))*J.prefixMinor (n+1)-J.data.aSq
(n+1)*J.prefixMinor n`.

Use: `«2610.05164v2».Jacobi.green_forward_identity` rewrites with this identity to establish
exact identity `J.prefixMinor (n+1)*J.green ⟨n,by omega⟩ j = Real.sqrt (J.data.aSq
(n+1))*J.prefixMinor n*J.green ⟨n+1,hn⟩ j`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.exists_representation`.

Proof: Use the identities/estimates `«2606.16671v2».JacobiData.leading_add_two` with the
arguments shown in the proof.
-/
theorem prefixMinor_recurrence (n : ℕ) : J.prefixMinor (n+2) =
    (1-J.data.b (n+1))*J.prefixMinor (n+1)-J.data.aSq (n+1)*J.prefixMinor n := by simp only [prefixMinor, J.data.leading_add_two, eval_sub, eval_mul, eval_X, eval_C]

/--
The stated quantitative bound `0 < J.prefixMinor n`.

Use: `«2610.05164v2».Jacobi.forwardRatio_pos` uses this bound to establish the stated
quantitative bound `0 < J.forwardRatio i`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.exists_representation`.

Proof: Use the identities/estimates `«2606.16671v2».JacobiData.matrix_principal_block`,
`«2606.16671v2».JacobiData.block_eq_charpoly` with the arguments shown in the proof.
-/
theorem prefixMinor_pos (hm : (1-J.matrix).PosDef) (n : ℕ) (hn : n ≤ N) :
    0 < J.prefixMinor n := by
  -- Use the identities/estimates `«2606.16671v2».JacobiData.matrix_principal_block`,
  -- `«2606.16671v2».JacobiData.block_eq_charpoly` with the arguments shown in the proof.
  let e : Fin n → Fin N := fun i => ⟨i.val,by omega⟩
  have hi : Function.Injective e := by
    intro i j he; apply Fin.ext; simpa [e] using congrArg Fin.val he
  have hp := hm.submatrix hi
  have he : (1-J.matrix).submatrix e e = 1-J.data.matrix 0 n := by
    simp only [Matrix.submatrix_sub, Pi.sub_apply]
    rw [Matrix.submatrix_one e hi]
    change 1-(J.data.matrix 0 N).submatrix e e = _
    have hh : (J.data.matrix 0 N).submatrix e e = J.data.matrix 0 n := by
      simpa only [Nat.zero_add] using J.data.matrix_principal_block N 0 n (by omega)
    rw [hh]
  rw [he] at hp
  have he : J.prefixMinor n = (1-J.data.matrix 0 n).det := by
    rw [prefixMinor, JacobiData.leading, J.data.block_eq_charpoly J.coupling_nonneg,
      Matrix.eval_charpoly]
    congr 1
  rw [he]; exact hp.det_pos

/--
Elimination of all rows preceding a site, directly from the true inverse.

Exact identity `J.prefixMinor (n+1)*J.green ⟨n,by omega⟩ j = Real.sqrt (J.data.aSq
(n+1))*J.prefixMinor n*J.green ⟨n+1,hn⟩ j`.

Use: `«2610.05164v2».Jacobi.green_forward` uses this identity to establish the identity
`J.green i j = J.forwardRatio i*J.green ⟨i.val+1,by omega⟩ j`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.exists_representation`.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem green_forward_identity (hm : (1-J.matrix).PosDef) (n : ℕ)
    (hn : n+1 < N) (j : Fin N) (hj : n < j.val) :
    J.prefixMinor (n+1)*J.green ⟨n,by omega⟩ j =
      Real.sqrt (J.data.aSq (n+1))*J.prefixMinor n*J.green ⟨n+1,hn⟩ j := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  induction n with
  | zero =>
    have he := J.green_row hm ⟨0,by omega⟩ j
    have hij : (⟨0,by omega⟩ : Fin N) ≠ j := by
      intro he
      have hh := congrArg Fin.val he
      change 0 = j.val at hh
      omega
    simp [hij, hn] at he
    simpa [J.prefixMinor_one] using sub_eq_zero.mp he
  | succ n ih =>
    have hi := ih (by omega) (by omega)
    have he := J.green_row hm ⟨n+1,by omega⟩ j
    have hij : (⟨n+1,by omega⟩ : Fin N) ≠ j := by
      intro he
      have hh := congrArg Fin.val he
      change n+1 = j.val at hh
      omega
    simp only [Nat.succ_pos, Nat.add_sub_cancel, hn, dite_true,
      hij, ite_false] at he
    rw [J.prefixMinor_recurrence]
    have hs := Real.sq_sqrt (J.coupling_nonneg (n+1))
    linear_combination J.prefixMinor (n+1)*he + Real.sqrt (J.data.aSq (n+1))*hi +
      J.prefixMinor n*J.green ⟨n+1,by omega⟩ j*hs

/--
Defines `forwardRatio` of type `(i : Fin N)` by `Real.sqrt (J.data.aSq (i.val+1))*
J.prefixMinor i.val/J.prefixMinor (i.val+1)`.

Use: `«2610.05164v2».Jacobi.green_forward` uses this definition to establish the identity
`J.green i j = J.forwardRatio i*J.green ⟨i.val+1,by omega⟩ j`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.exists_representation`.
-/
def forwardRatio (i : Fin N) := Real.sqrt (J.data.aSq (i.val+1))*
  J.prefixMinor i.val/J.prefixMinor (i.val+1)

/--
The stated quantitative bound `0 < J.forwardRatio i`.

Use: `«2610.05164v2».Jacobi.green_entry_pos_of_le` uses this bound to establish the stated
quantitative bound `0 < J.green i j`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.exists_representation`.

Proof: Use the identities/estimates `«2610.05164v2».Jacobi.prefixMinor_pos` with the arguments
shown in the proof.
-/
theorem forwardRatio_pos (hm : (1-J.matrix).PosDef) (hir : J.Irreducible)
    (i : Fin N) (hi : i.val+1 < N) : 0 < J.forwardRatio i :=
  div_pos (mul_pos (Real.sqrt_pos.mpr (hir _ (by omega) hi))
    (J.prefixMinor_pos hm i.val (by omega))) (J.prefixMinor_pos hm (i.val+1) (by omega))

/--
Exact identity `J.green i j = J.forwardRatio i*J.green ⟨i.val+1,by omega⟩ j`.

Use: `«2610.05164v2».Jacobi.green_entry_pos_of_le` rewrites with this identity to establish the
stated quantitative bound `0 < J.green i j`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.exists_representation`.

Proof: Use the identities/estimates `«2610.05164v2».Jacobi.green_forward_identity`,
`«2610.05164v2».Jacobi.prefixMinor_pos` with the arguments shown in the proof.
-/
theorem green_forward (hm : (1-J.matrix).PosDef) (i j : Fin N) (hij : i.val < j.val) :
    J.green i j = J.forwardRatio i*J.green ⟨i.val+1,by omega⟩ j := by
  have he := J.green_forward_identity hm i.val (by omega) j hij
  dsimp [forwardRatio]
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (J.prefixMinor_pos hm (i.val+1) (by omega)).ne').mpr
  convert he using 1; ring

end
end «2610.05164v2».Jacobi
