import «2610.05164v2».Green.Contractivity
import «2610.05164v2».Finite.Restriction
import «2606.16671v2».Jacobi.Resolvent
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
Article: 2610.05164v2, Theorem 2.3.
The Green inverse really splits at every zero edge.
Use: `«2610.05164v2».Jacobi.zero_edge_green` feeds `«2610.05164v2».Packing.exists_representation`
(Every contractive Jacobi chain has the article's interval packing, including all reducible chains).
Proof chain: `«2610.05164v2».Packing.exists_representation` — 2610.05164v2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
-/
namespace «2610.05164v2».Jacobi
noncomputable section
open «2606.16671v2» Matrix Real
open scoped Matrix
set_option backward.isDefEq.respectTransparency true

variable {N : ℕ} (J : Jacobi N)

/--
Canonical Jacobi chain of a contiguous principal segment.

Use: `«2610.05164v2».Jacobi.segment_contractive` uses this definition to establish the stated
quantitative bound `«2606.16671v2».opNorm (J.segment a n).matrix < 1`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.exists_representation`.
-/
def segment (a n : ℕ) : Jacobi n where
  data.b i := if i < n then J.data.b (a+i) else 0
  data.aSq i := if 0 < i ∧ i < n then J.data.aSq (a+i) else 0
  coupling_nonneg i := by
    change 0 ≤ if 0 < i ∧ i < n then J.data.aSq (a+i) else 0
    split_ifs <;> first | exact J.coupling_nonneg _ | exact le_rfl
  coupling_zero := by simp
  diagonal_tail i hi := by simp [not_lt.mpr hi]
  coupling_tail i hi := by simp [not_lt.mpr hi]

/--
Exact identity `(J.segment a n).matrix = J.data.matrix a n`.

Use: `«2610.05164v2».Jacobi.segment_principal` rewrites with this identity to establish exact
identity `J.matrix.submatrix (fun i : Fin n => (⟨a+i.val,by omega⟩ : Fin N)) (fun i : Fin n =>
(⟨a+i.val,by omega⟩ : Fin N)) = (J.segment a n).matrix`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.exists_representation`.

Proof: Use the identities/estimates `«2606.16671v2».JacobiData.matrix_apply` with the arguments
shown in the proof.
-/
theorem segment_matrix (a n : ℕ) : (J.segment a n).matrix = J.data.matrix a n := by
  ext i j
  simp only [matrix,«2606.16671v2».JacobiData.matrix_apply,segment,Nat.zero_add]
  split_ifs <;> simp_all

/--
Exact identity `J.matrix.submatrix (fun i : Fin n => (⟨a+i.val,by omega⟩ : Fin N)) (fun i : Fin
n => (⟨a+i.val,by omega⟩ : Fin N)) = (J.segment a n).matrix`.

Use: `«2610.05164v2».Jacobi.segment_contractive` uses this identity to establish the stated
quantitative bound `«2606.16671v2».opNorm (J.segment a n).matrix < 1`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.exists_representation`.

Proof: Use the identities/estimates `«2610.05164v2».Jacobi.segment_matrix`,
`«2606.16671v2».JacobiData.matrix_principal_block` with the arguments shown in the proof.
-/
theorem segment_principal (a n : ℕ) (hn : a+n ≤ N) :
    J.matrix.submatrix (fun i : Fin n => (⟨a+i.val,by omega⟩ : Fin N))
      (fun i : Fin n => (⟨a+i.val,by omega⟩ : Fin N)) = (J.segment a n).matrix := by
  rw [segment_matrix]
  exact J.data.matrix_principal_block N a n hn

/--
The stated quantitative bound `«2606.16671v2».opNorm (J.segment a n).matrix < 1`.

Use: `«2610.05164v2».Jacobi.zero_edge_green` uses this bound to establish the identity stated
in that declaration.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.exists_representation`.

Proof: Use the identities/estimates `«2610.05164v2».Jacobi.pencils_of_contractive`,
`«2610.05164v2».Jacobi.contractive_of_pencils`, `«2610.05164v2».Jacobi.segment_principal` with
the arguments shown in the proof.
-/
theorem segment_contractive (h : «2606.16671v2».opNorm J.matrix < 1) (a n : ℕ) (hn : a+n ≤ N) :
    «2606.16671v2».opNorm (J.segment a n).matrix < 1 := by
  -- Use the identities/estimates `«2610.05164v2».Jacobi.pencils_of_contractive`,
  -- `«2610.05164v2».Jacobi.contractive_of_pencils`, `«2610.05164v2».Jacobi.segment_principal`
  -- with the arguments shown in the proof.
  obtain ⟨hm,hp⟩ := J.pencils_of_contractive h
  have hi : Function.Injective (fun i : Fin n => (⟨a+i.val,by omega⟩ : Fin N)) := by
    intro i j he
    apply Fin.ext
    have hh := congrArg Fin.val he
    dsimp at hh
    omega
  apply (J.segment a n).contractive_of_pencils
  · have ht := hm.submatrix hi
    rw [Matrix.submatrix_sub] at ht
    change ((1 : Matrix (Fin N) (Fin N) ℝ).submatrix _ _ - J.matrix.submatrix _ _).PosDef at ht
    rwa [Matrix.submatrix_one _ hi,J.segment_principal a n hn] at ht
  · have ht := hp.submatrix hi
    rw [Matrix.submatrix_add] at ht
    change ((1 : Matrix (Fin N) (Fin N) ℝ).submatrix _ _ + J.matrix.submatrix _ _).PosDef at ht
    rwa [Matrix.submatrix_one _ hi,J.segment_principal a n hn] at ht

/--
Splitting a zero edge gives a genuine block diagonal pencil.

Exact identity `(1-J.matrix).submatrix («2606.16671v2».JacobiData.splitIndex N ⟨k,by omega⟩)
(«2606.16671v2».JacobiData.splitIndex N ⟨k,by omega⟩) = Matrix.fromBlocks (1-(J.segment 0
k).matrix) 0 0 (1-(J.segment k (N-k)).matrix)`.

Use: `«2610.05164v2».Jacobi.zero_edge_green` rewrites with this identity to establish the
identity stated in that declaration.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.exists_representation`.

Proof: Use the identities/estimates `«2610.05164v2».Jacobi.segment_matrix`,
`«2606.16671v2».JacobiData.splitIndex_left`, `«2606.16671v2».JacobiData.splitIndex_right` with
the arguments shown in the proof.
-/
theorem zero_edge_pencil (k : ℕ) (hk : k ≤ N) (hz : J.data.aSq k = 0) :
    (1-J.matrix).submatrix («2606.16671v2».JacobiData.splitIndex N ⟨k,by omega⟩)
      («2606.16671v2».JacobiData.splitIndex N ⟨k,by omega⟩) =
      Matrix.fromBlocks (1-(J.segment 0 k).matrix) 0 0 (1-(J.segment k (N-k)).matrix) := by
  -- Use the identities/estimates `«2610.05164v2».Jacobi.segment_matrix`,
  -- `«2606.16671v2».JacobiData.splitIndex_left`, `«2606.16671v2».JacobiData.splitIndex_right`
  -- with the arguments shown in the proof.
  rw [J.segment_matrix,J.segment_matrix]
  have he (n a : ℕ) : (1-J.data.matrix a n) = Matrix.scalar (Fin n) 1-J.data.matrix a n := by simp [Matrix.scalar]
  change (1-J.data.matrix 0 N).submatrix _ _ = _
  rw [he,he,he]
  have hl (i : Fin k) : («2606.16671v2».JacobiData.splitIndex N ⟨k,by omega⟩ (Sum.inl i)).val = i.val :=
    «2606.16671v2».JacobiData.splitIndex_left N ⟨k,by omega⟩ i
  have hr (i : Fin (N-k)) : («2606.16671v2».JacobiData.splitIndex N ⟨k,by omega⟩ (Sum.inr i)).val = k+i.val :=
    «2606.16671v2».JacobiData.splitIndex_right N ⟨k,by omega⟩ i
  ext i j
  cases i <;> cases j <;>
    simp only [Matrix.submatrix_apply,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,J.data.shifted_apply,Fin.ext_iff,
      hl,hr,Nat.zero_add,Matrix.zero_apply]
  all_goals split_ifs <;> try first | rfl | omega
  · rename_i i j _hne _hadj
    have he : k+j.val = k := by omega
    rw [he,hz,sqrt_zero,neg_zero]
  · rename_i i j _hne _hnadj _hadj
    have he : k+i.val = k := by omega
    rw [he,hz,sqrt_zero,neg_zero]

/--
The Green inverse really splits at every zero edge.

Exact identity `J.green.submatrix («2606.16671v2».JacobiData.splitIndex N ⟨k,by omega⟩)
(«2606.16671v2».JacobiData.splitIndex N ⟨k,by omega⟩) = Matrix.fromBlocks (J.segment 0 k).green
0 0 (J.segment k (N-k)).green`.

Use: `«2610.05164v2».Packing.exists_representation` uses this identity to establish the precise
assertion is `Nonempty (Representation J.green gap)`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.exists_representation`.

Proof: Use the identities/estimates `«2610.05164v2».Jacobi.zero_edge_pencil`,
`«2610.05164v2».Jacobi.pencils_of_contractive`, `«2610.05164v2».Jacobi.segment_contractive`
with the arguments shown in the proof.
-/
theorem zero_edge_green (h : «2606.16671v2».opNorm J.matrix < 1) (k : ℕ) (hk : k ≤ N) (hz : J.data.aSq k = 0) :
    J.green.submatrix («2606.16671v2».JacobiData.splitIndex N ⟨k,by omega⟩)
      («2606.16671v2».JacobiData.splitIndex N ⟨k,by omega⟩) =
      Matrix.fromBlocks (J.segment 0 k).green 0 0 (J.segment k (N-k)).green := by
  -- Use the identities/estimates `«2610.05164v2».Jacobi.zero_edge_pencil`,
  -- `«2610.05164v2».Jacobi.pencils_of_contractive`,
  -- `«2610.05164v2».Jacobi.segment_contractive` with the arguments shown in the proof.
  rw [green,← Matrix.inv_submatrix_equiv,J.zero_edge_pencil k hk hz]
  have hL := ((J.segment 0 k).pencils_of_contractive (J.segment_contractive h 0 k (by omega))).1.isUnit
  have hR := ((J.segment k (N-k)).pencils_of_contractive (J.segment_contractive h k (N-k) (by omega))).1.isUnit
  rw [Matrix.inv_fromBlocks_zero₂₁_of_isUnit_iff _ _ _ (iff_of_true hL hR)]
  simp only [Matrix.mul_zero,Matrix.zero_mul,neg_zero,green]

end
end «2610.05164v2».Jacobi
