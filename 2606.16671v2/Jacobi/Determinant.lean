import «2606.16671v2».Jacobi.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
Article: 2606.16671v2, Theorem 4.2.
Every recurrence block is the characteristic polynomial of the actual Jacobi block.
Use: `«2606.16671v2».JacobiData.block_eq_charpoly` feeds `«2606.16671v2».JacobiData.reversed_block`
(reversed block).
Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — Jacobi
characteristic-polynomial recurrence. The needed form is proved here.
-/
namespace «2606.16671v2»
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped Matrix

/--
Append a site, linked only to the preceding final site.

Use: `«2606.16671v2».JacobiData.block_eq_charpoly` uses this definition to establish exact
identity `J.block a n = (J.matrix a n).charpoly`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.spectrum_eq_nodes`.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — Jacobi
characteristic-polynomial recurrence.
-/
def extendTridiagonal {R : Type*} [Zero R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (diag link : R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  let tailLink := fun i : Fin n => if i.val + 1 = n then link else 0
  fun i j => Fin.lastCases (Fin.lastCases diag tailLink j)
    (fun i => Fin.lastCases (tailLink i) (fun j => M i j) j) i

/--
Exact identity `extendTridiagonal M diag link (Fin.last n) (Fin.last n) = diag`.

Use: `«2606.16671v2».JacobiData.block_eq_charpoly` uses this identity to establish exact
identity `J.block a n = (J.matrix a n).charpoly`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.spectrum_eq_nodes`.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — Jacobi
characteristic-polynomial recurrence.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[simp] theorem extendTridiagonal_last_last {R : Type*} [Zero R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (diag link : R) :
    extendTridiagonal M diag link (Fin.last n) (Fin.last n) = diag := by simp [extendTridiagonal]

/--
Exact identity `extendTridiagonal M diag link (Fin.last n) j.castSucc = if j.val + 1 = n then
link else 0`.

Use: `«2606.16671v2».JacobiData.matrix_apply` rewrites with this identity to establish exact
identity `J.matrix a n i j = if i = j then J.b (a + i.val) else if i.val + 1 = j.val then
Real.sqrt (J.aSq (a + j.val)) else if j.val + 1 = i.val then Real.sqrt (J.aSq (a + i.val)) else
0`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.spectrum_eq_nodes`.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — Jacobi
characteristic-polynomial recurrence.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[simp] theorem extendTridiagonal_last_castSucc {R : Type*} [Zero R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (diag link : R) (j : Fin n) :
    extendTridiagonal M diag link (Fin.last n) j.castSucc =
      if j.val + 1 = n then link else 0 := by simp [extendTridiagonal]

/--
Exact identity `extendTridiagonal M diag link i.castSucc (Fin.last n) = if i.val + 1 = n then
link else 0`.

Use: `«2606.16671v2».JacobiData.matrix_apply` rewrites with this identity to establish exact
identity `J.matrix a n i j = if i = j then J.b (a + i.val) else if i.val + 1 = j.val then
Real.sqrt (J.aSq (a + j.val)) else if j.val + 1 = i.val then Real.sqrt (J.aSq (a + i.val)) else
0`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.spectrum_eq_nodes`.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — Jacobi
characteristic-polynomial recurrence.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[simp] theorem extendTridiagonal_castSucc_last {R : Type*} [Zero R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (diag link : R) (i : Fin n) :
    extendTridiagonal M diag link i.castSucc (Fin.last n) =
      if i.val + 1 = n then link else 0 := by simp [extendTridiagonal]

/--
Exact identity `extendTridiagonal M diag link i.castSucc j.castSucc = M i j`.

Use: `«2606.16671v2».JacobiData.matrix_apply` uses this identity to establish the identity
`J.matrix a n i j = if i = j then J.b (a + i.val) else if i.val + 1 = j.val then Real.sqrt
(J.aSq (a + j.val)) else if j.val + 1 = i.val then Real.sqrt (J.aSq (a + i.val)) else 0`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.spectrum_eq_nodes`.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — Jacobi
characteristic-polynomial recurrence.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[simp] theorem extendTridiagonal_castSucc_castSucc {R : Type*} [Zero R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (diag link : R) (i j : Fin n) :
    extendTridiagonal M diag link i.castSucc j.castSucc = M i j := by simp [extendTridiagonal]

/--
Exact identity `Matrix.charmatrix (extendTridiagonal M diag link) = extendTridiagonal
M.charmatrix (X - C diag) (-C link)`.

Use: `«2606.16671v2».JacobiData.pencil_eq_charMatrix` rewrites with this identity to establish
exact identity `J.pencil a n = Matrix.charmatrix (J.matrix a n)`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.spectrum_eq_nodes`.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — Jacobi
characteristic-polynomial recurrence.

Proof: Use the identities/estimates `«2606.16671v2».extendTridiagonal_last_last`,
`«2606.16671v2».extendTridiagonal_last_castSucc`,
`«2606.16671v2».extendTridiagonal_castSucc_last` with the arguments shown in the proof.
-/
theorem charmatrix_extendTridiagonal {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (diag link : R) :
    Matrix.charmatrix (extendTridiagonal M diag link) =
      extendTridiagonal M.charmatrix (X - C diag) (-C link) := by
  -- Use the identities/estimates `«2606.16671v2».extendTridiagonal_last_last`,
  -- `«2606.16671v2».extendTridiagonal_last_castSucc`,
  -- `«2606.16671v2».extendTridiagonal_castSucc_last` with the arguments shown in the proof.
  apply Matrix.ext
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [Matrix.charmatrix_apply_eq, extendTridiagonal_last_last]
  · rw [Matrix.charmatrix_apply_ne _ _ _ (Ne.symm (Fin.castSucc_ne_last _))]
    simp only [extendTridiagonal_last_castSucc, apply_ite, map_zero]
    split_ifs <;> simp
  · rw [Matrix.charmatrix_apply_ne _ _ _ (Fin.castSucc_ne_last _)]
    simp only [extendTridiagonal_castSucc_last, apply_ite, map_zero]
    split_ifs <;> simp
  · simp [Matrix.charmatrix_apply, Matrix.diagonal]

/--
Exact identity `(extendTridiagonal M diag link).submatrix Fin.castSucc Fin.castSucc = M`.

Use: `«2606.16671v2».JacobiData.block_eq_charpoly` rewrites with this identity to establish
exact identity `J.block a n = (J.matrix a n).charpoly`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.spectrum_eq_nodes`.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — Jacobi
characteristic-polynomial recurrence.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem extendTridiagonal_tail {R : Type*} [Zero R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (diag link : R) :
    (extendTridiagonal M diag link).submatrix Fin.castSucc Fin.castSucc = M := by
  ext i j
  simp [extendTridiagonal, Matrix.submatrix_apply]

/--
Exact identity `((extendTridiagonal M diag link).submatrix Fin.castSucc (Fin.succAbove
(Fin.castSucc (Fin.last n)))).det = link * (M.submatrix Fin.castSucc Fin.castSucc).det`.

Use: `«2606.16671v2».extendTridiagonal_det` rewrites with this identity to establish exact
identity `(extendTridiagonal M diag link).det = diag * M.det - link ^ 2 * (M.submatrix
Fin.castSucc Fin.castSucc).det`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.spectrum_eq_nodes`.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — Jacobi
characteristic-polynomial recurrence.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem extendTridiagonal_minor {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (diag link : R) :
    ((extendTridiagonal M diag link).submatrix Fin.castSucc
      (Fin.succAbove (Fin.castSucc (Fin.last n)))).det =
      link * (M.submatrix Fin.castSucc Fin.castSucc).det := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  let B := (extendTridiagonal M diag link).submatrix Fin.castSucc
    (Fin.succAbove (Fin.castSucc (Fin.last n)))
  have hlast : B (Fin.last n) (Fin.last n) = link := by simp [B, extendTridiagonal, Matrix.submatrix_apply]
  have hzero (i : Fin n) : B i.castSucc (Fin.last n) = 0 := by
    simp [B, extendTridiagonal, Matrix.submatrix_apply]; grind
  have hminor : B.submatrix Fin.castSucc Fin.castSucc =
      M.submatrix Fin.castSucc Fin.castSucc := by ext; simp [B, extendTridiagonal, Matrix.submatrix_apply]
  change B.det = _
  simp [Matrix.det_succ_column B (Fin.last n), Fin.sum_univ_castSucc, hlast, hzero, hminor]

/--
The continuant determinant recurrence, valid over any commutative ring.

Exact identity `(extendTridiagonal M diag link).det = diag * M.det - link ^ 2 * (M.submatrix
Fin.castSucc Fin.castSucc).det`.

Use: `«2606.16671v2».JacobiData.block_eq_charpoly` rewrites with this identity to establish
exact identity `J.block a n = (J.matrix a n).charpoly`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.spectrum_eq_nodes`.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — Jacobi
characteristic-polynomial recurrence.

Proof: Use the identities/estimates `«2606.16671v2».extendTridiagonal_last_castSucc`,
`«2606.16671v2».extendTridiagonal_last_last`, `«2606.16671v2».extendTridiagonal_tail` with the
arguments shown in the proof.
-/
theorem extendTridiagonal_det {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (diag link : R) :
    (extendTridiagonal M diag link).det = diag * M.det -
      link ^ 2 * (M.submatrix Fin.castSucc Fin.castSucc).det := by
  -- Use the identities/estimates `«2606.16671v2».extendTridiagonal_last_castSucc`,
  -- `«2606.16671v2».extendTridiagonal_last_last`, `«2606.16671v2».extendTridiagonal_tail` with
  -- the arguments shown in the proof.
  rw [Matrix.det_succ_row (extendTridiagonal M diag link) (Fin.last _), Fin.sum_univ_castSucc]
  simp only [extendTridiagonal_last_last, extendTridiagonal_last_castSucc,
    extendTridiagonal_tail, Fin.val_last, Fin.val_castSucc, Fin.succAbove_last]
  rw [Finset.sum_eq_single_of_mem (Fin.last n) (Finset.mem_univ _)]
  · rw [ite_eq_left (by rfl), extendTridiagonal_minor, Fin.val_last,
      Odd.neg_one_pow ⟨n, by ring⟩, Even.neg_one_pow ⟨n + 1, rfl⟩]
    ring
  · intro b _ hb
    rw [ite_eq_right (fun h => hb (Fin.ext (by rw [Fin.val_last]; omega)))]
    ring

namespace JacobiData

/--
Defines `matrix` by pattern matching with result type `(n : ℕ) → Matrix (Fin n) (Fin n) ℝ`. The
displayed branches determine the recursive cases and their returned values.

Use: `«2606.16671v2».JacobiData.matrix_apply` rewrites with this definition to establish exact
identity `J.matrix a n i j = if i = j then J.b (a + i.val) else if i.val + 1 = j.val then
Real.sqrt (J.aSq (a + j.val)) else if j.val + 1 = i.val then Real.sqrt (J.aSq (a + i.val)) else
0`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.gain_exact_resolvent`.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — Jacobi
characteristic-polynomial recurrence.
-/
def matrix (J : JacobiData) (a : ℕ) : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ
  | 0 => 0
  | n + 1 => extendTridiagonal (J.matrix a n) (J.b (a + n)) (Real.sqrt (J.aSq (a + n)))

/--
Defines `pencil` by pattern matching with result type `(n : ℕ) → Matrix (Fin n) (Fin n) ℝ[X]`.
The displayed branches determine the recursive cases and their returned values.

Use: `«2606.16671v2».JacobiData.block_eq_charpoly` rewrites with this definition to establish
exact identity `J.block a n = (J.matrix a n).charpoly`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.spectrum_eq_nodes`.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — Jacobi
characteristic-polynomial recurrence.
-/
def pencil (J : JacobiData) (a : ℕ) : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ[X]
  | 0 => 0
  | n + 1 => extendTridiagonal (J.pencil a n) (X - C (J.b (a + n)))
      (-C (Real.sqrt (J.aSq (a + n))))

/--
Exact identity `J.matrix a n i j = if i = j then J.b (a + i.val) else if i.val + 1 = j.val then
Real.sqrt (J.aSq (a + j.val)) else if j.val + 1 = i.val then Real.sqrt (J.aSq (a + i.val)) else
0`.

Use: `«2606.16671v2».JacobiData.matrix_isHermitian` rewrites with this identity to establish
the precise assertion is `(J.matrix a n).IsHermitian`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.kernel_abs_le_endpoint`.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — Jacobi
characteristic-polynomial recurrence.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem matrix_apply (J : JacobiData) (a n : ℕ) (i j : Fin n) :
    J.matrix a n i j = if i = j then J.b (a + i.val)
      else if i.val + 1 = j.val then Real.sqrt (J.aSq (a + j.val))
      else if j.val + 1 = i.val then Real.sqrt (J.aSq (a + i.val)) else 0 := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [matrix]
    · simp only [matrix, extendTridiagonal_last_castSucc, Fin.val_last, Fin.val_castSucc,
        ite_eq_right (Ne.symm (Fin.castSucc_ne_last _)), ite_eq_right (show n + 1 ≠ j.val by omega)]
    · simp only [matrix, extendTridiagonal_castSucc_last, Fin.val_last, Fin.val_castSucc,
        ite_eq_right (Fin.castSucc_ne_last _)]
      split_ifs <;> simp_all
      omega
    · simpa [matrix, Fin.castSucc_inj] using ih i j

/--
The precise assertion is `(J.matrix a n).IsHermitian`.

Use: `«2606.16671v2».JacobiData.leading_orthogonality` uses this assertion to establish the
precise assertion is `let B`.

Article: 2606.16671v2, Corollary 5.3 via `«2606.16671v2».SineJacobi.G_exact`.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — Jacobi
characteristic-polynomial recurrence.

Proof: Separate `i = j` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem matrix_isHermitian (J : JacobiData) (a n : ℕ) : (J.matrix a n).IsHermitian := by
  -- Separate `i = j` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  apply Matrix.ext
  intro i j
  simp only [Matrix.transpose_apply, matrix_apply]
  by_cases hij : i = j
  · subst j; simp
  · simp only [ite_eq_right hij, ite_eq_right (Ne.symm hij)]
    split_ifs <;> first | rfl | omega

/--
Independently built contiguous blocks are actual principal submatrices of the full chain.

Exact identity `(J.matrix 0 N).submatrix (fun i : Fin n => (⟨a + i.val, by omega⟩ : Fin N))
(fun i : Fin n => (⟨a + i.val, by omega⟩ : Fin N)) = J.matrix a n`.

Use: `«2606.16671v2».JacobiData.block_eval_pos_of_spectrum` rewrites with this identity to
establish the stated quantitative bound `0 < (J.block a n).eval eta`.

Article: 2606.16671v2, Corollary 5.3 via `«2606.16671v2».SineJacobi.G_exact`.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — Jacobi
characteristic-polynomial recurrence.

Proof: Use the identities/estimates `«2606.16671v2».JacobiData.matrix_apply` with the arguments
shown in the proof.
-/
theorem matrix_principal_block (J : JacobiData) (N a n : ℕ) (hn : a + n ≤ N) :
    (J.matrix 0 N).submatrix (fun i : Fin n => (⟨a + i.val, by omega⟩ : Fin N))
      (fun i : Fin n => (⟨a + i.val, by omega⟩ : Fin N)) = J.matrix a n := by
  apply Matrix.ext
  intro i j
  simp [Matrix.submatrix_apply, matrix_apply, Fin.ext_iff, Nat.add_assoc]

/--
Exact identity `J.pencil a n = Matrix.charmatrix (J.matrix a n)`.

Use: `«2606.16671v2».JacobiData.block_eq_charpoly` rewrites with this identity to establish
exact identity `J.block a n = (J.matrix a n).charpoly`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.spectrum_eq_nodes`.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — Jacobi
characteristic-polynomial recurrence.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem pencil_eq_charMatrix (J : JacobiData) (a n : ℕ) :
    J.pencil a n = Matrix.charmatrix (J.matrix a n) := by
  induction n with
  | zero => ext i; exact Fin.elim0 i
  | succ n ih =>
    rw [matrix, charmatrix_extendTridiagonal, pencil, ih]

/--
Every recurrence block is the characteristic polynomial of the actual Jacobi block.

Exact identity `J.block a n = (J.matrix a n).charpoly`.

Use: `«2606.16671v2».JacobiData.block_eval_pos_of_spectrum` rewrites with this identity to
establish the stated quantitative bound `0 < (J.block a n).eval eta`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.spectrum_eq_nodes`.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — Jacobi
characteristic-polynomial recurrence.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem block_eq_charpoly (J : JacobiData) (hsq : ∀ s, 0 ≤ J.aSq s) (a n : ℕ) :
    J.block a n = (J.matrix a n).charpoly := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  change J.block a n = (Matrix.charmatrix (J.matrix a n)).det
  rw [← pencil_eq_charMatrix]
  induction n using Nat.twoStepInduction with
  | zero => simp [block, pencil]
  | one =>
    rw [block, pencil, Matrix.det_unique]
    change X - C (J.b a) = extendTridiagonal (J.pencil a 0)
      (X - C (J.b (a + 0))) (-C (Real.sqrt (J.aSq (a + 0)))) (Fin.last 0) (Fin.last 0)
    exact (extendTridiagonal_last_last _ _ _).symm
  | more n ih0 ih1 =>
    have ht : (J.pencil a (n + 1)).submatrix Fin.castSucc Fin.castSucc = J.pencil a n := by
      rw [pencil, extendTridiagonal_tail]
    rw [pencil, extendTridiagonal_det, ht, ← ih1, ← ih0, block]
    have hc : (-C (Real.sqrt (J.aSq (a + n + 1)))) ^ 2 = C (J.aSq (a + n + 1)) := by
      rw [neg_sq, ← map_pow, Real.sq_sqrt (hsq _)]
    simpa only [Nat.add_assoc] using congrArg
      (fun q => (X - C (J.b (a + n + 1))) * J.block a (n + 1) - q * J.block a n) hc.symm

end JacobiData
end
end «2606.16671v2»
