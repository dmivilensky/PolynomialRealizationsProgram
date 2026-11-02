import jacobi.Finite.PaddedClosedSpectrum
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
Concrete restarted block competitors for the full Nesterov polynomial.
Appending minus-one singletons gives a genuine nonnegative-link Jacobi
chain. Its characteristic polynomial and its Green energy split exactly.
Use: AllThreeTerm obtains the matching sharp symmetric limit, and
NesterovComparisons transfers the strict standard-flow improvement to blocks.
Article: jacobi, Theorem 5.3 and Corollary 5.7.
Article role: genuine padded block competitors and their full-horizon endpoint normalization.
-/
namespace jacobi.Finite
noncomputable section
open chebyshev1 chebyshev2 Matrix Polynomial
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

/-- Append exactly L Landweber singleton blocks to an actual Jacobi
chain. The old incoming-link sequence already vanishes from index N on.
Article: jacobi, Theorem 5.3 and Corollary 5.7.
-/
def appendMinusOne {N : ℕ} (J : Jacobi N) (L : ℕ) : Jacobi (N+L) where
  data := {
    b := fun i => if i < N then J.data.b i else if i < N+L then -1 else 0
    aSq := J.data.aSq }
  coupling_nonneg := J.coupling_nonneg
  coupling_zero := J.coupling_zero
  diagonal_tail i hi := by simp [not_lt.mpr hi,show ¬i < N from by omega]
  coupling_tail i hi := J.coupling_tail i (by omega)

/-- The original principal block is unchanged, entry by entry.
Article: jacobi, Theorem 5.3 and Corollary 5.7.
-/
theorem appendMinusOne_left {N : ℕ} (J : Jacobi N) (L : ℕ) (i j : Fin N) :
    (appendMinusOne J L).matrix (Fin.castAdd L i) (Fin.castAdd L j)=J.matrix i j := by
  simp [Jacobi.matrix,JacobiData.matrix_apply,appendMinusOne,i.isLt]

/-- Every appended block is the scalar minus one with zero momentum.
Article: jacobi, Theorem 5.3 and Corollary 5.7.
-/
theorem appendMinusOne_right {N : ℕ} (J : Jacobi N) (L : ℕ) (i j : Fin L) :
    (appendMinusOne J L).matrix (Fin.natAdd N i) (Fin.natAdd N j)=
      (-1 : Matrix (Fin L) (Fin L) ℝ) i j := by
  have hi : N+i.val < N+L := by omega
  have hai := J.coupling_tail (N+i.val) (by omega)
  have haj := J.coupling_tail (N+j.val) (by omega)
  simp [Jacobi.matrix,JacobiData.matrix_apply,appendMinusOne,
    show ¬N+i.val < N from by omega,hi,hai,haj,Matrix.one_apply]
  split_ifs <;> norm_num

/-- The old chain and the appended singleton chains are separated by
a literal zero link, including at the first appended site.
Article: jacobi, Theorem 5.3 and Corollary 5.7.
-/
theorem appendMinusOne_cross {N : ℕ} (J : Jacobi N) (L : ℕ) (i : Fin N) (j : Fin L) :
    (appendMinusOne J L).matrix (Fin.castAdd L i) (Fin.natAdd N j)=0 := by
  have hne : Fin.castAdd L i≠Fin.natAdd N j := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_castAdd,Fin.val_natAdd] at hval
    omega
  have hj := J.coupling_tail (N+j.val) (by omega)
  simp [Jacobi.matrix,JacobiData.matrix_apply,appendMinusOne,hne,hj,
    show ¬N+j.val+1=i.val from by omega]

/-- Reindexing by the canonical finite sum equivalence gives exactly
the block diagonal matrix. The spectral and energy identities use this
actual matrix equality rather than a proposed block representation.
Article: jacobi, Theorem 5.3 and Corollary 5.7.
-/
theorem appendMinusOne_matrix {N : ℕ} (J : Jacobi N) (L : ℕ) :
    reindex finSumFinEquiv.symm finSumFinEquiv.symm (appendMinusOne J L).matrix=
      fromBlocks J.matrix 0 0 (-1 : Matrix (Fin L) (Fin L) ℝ) := by
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j => exact appendMinusOne_left J L i j
    | inr j => exact appendMinusOne_cross J L i j
  | inr i =>
    cases j with
    | inl j =>
      change (appendMinusOne J L).matrix (Fin.natAdd N i) (Fin.castAdd L j)=0
      rw [← (appendMinusOne J L).matrix_isHermitian.isSymm.apply
        (Fin.natAdd N i) (Fin.castAdd L j),appendMinusOne_cross]
    | inr j => exact appendMinusOne_right J L i j

/-- The literal block belongs to the full repeated-root fibre.
Article: jacobi, Theorem 5.3 and Corollary 5.7.
-/
theorem Nodes.appendMinusOne_mem {N : ℕ} (S : Nodes N) {J : Jacobi N}
    (hJ : InFiber J S.polynomial) (L : ℕ) :
    InClosedFiber (appendMinusOne J L) (S.padMinusOne L).polynomial := by
  change (appendMinusOne J L).matrix.charpoly=_
  rw [← Matrix.charpoly_reindex finSumFinEquiv.symm,appendMinusOne_matrix,
    Matrix.charpoly_fromBlocks_zero₁₂,hJ.2,S.padMinusOne_polynomial]
  congr 1
  rw [show (-1 : Matrix (Fin L) (Fin L) ℝ)=diagonal (fun _ => (-1:ℝ)) by
    simp only [← Matrix.diagonal_one,Matrix.diagonal_neg],Matrix.charpoly_diagonal]
  simp

/-- In the block coordinates, the endpoint pencil is the old pencil
and the scalar matrix two.
Article: jacobi, Theorem 5.3 and Corollary 5.7.
-/
theorem appendMinusOne_pencil {N : ℕ} (J : Jacobi N) (L : ℕ) :
    reindex finSumFinEquiv.symm finSumFinEquiv.symm (1-(appendMinusOne J L).matrix)=
      fromBlocks (1-J.matrix) 0 0 (2 : Matrix (Fin L) (Fin L) ℝ) := by
  change (Matrix.reindexRingEquiv ℝ finSumFinEquiv.symm) (1-(appendMinusOne J L).matrix)=_
  rw [map_sub,map_one]
  change 1-reindex finSumFinEquiv.symm finSumFinEquiv.symm (appendMinusOne J L).matrix=_
  rw [appendMinusOne_matrix,show (2 : Matrix (Fin L) (Fin L) ℝ)=(2:ℝ) • 1 by
    norm_num [two_smul ℝ]]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp [Matrix.one_apply]
  · simp
  · simp
  · by_cases h : i=j <;> norm_num [h]

/-- The inverse pencil splits exactly across the restart. Each extra
minus-one root contributes Green diagonal one half.
Article: jacobi, Theorem 5.3 and Corollary 5.7.
-/
theorem appendMinusOne_green {N : ℕ} (J : Jacobi N) (hp : (1-J.matrix).PosDef) (L : ℕ) :
    reindex finSumFinEquiv.symm finSumFinEquiv.symm (appendMinusOne J L).green=
      fromBlocks J.green 0 0 ((1/2:ℝ) • (1 : Matrix (Fin L) (Fin L) ℝ)) := by
  rw [Jacobi.green,← Matrix.inv_reindex,appendMinusOne_pencil]
  have htwo : (2 : Matrix (Fin L) (Fin L) ℝ)=(2:ℝ) • 1 := by
    norm_num [two_smul ℝ]
  have h2 : IsUnit (2 : Matrix (Fin L) (Fin L) ℝ) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [htwo,Matrix.det_smul,Matrix.det_one,mul_one]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
  rw [Matrix.inv_fromBlocks_zero₁₂_of_isUnit_iff _ _ _ (by
    exact iff_of_true ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hp.det_pos.ne')) h2)]
  simp only [Matrix.zero_mul,Matrix.mul_zero,neg_zero,Jacobi.green]
  congr 1
  apply Matrix.inv_eq_left_inv
  rw [htwo,Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,smul_smul]
  norm_num

/-- The true block energy is the original energy plus L/4, including
degree zero and every finite number of singleton restart steps.
Article: jacobi, Theorem 5.3 and Corollary 5.7.
-/
theorem appendMinusOne_energy {N : ℕ} (J : Jacobi N) (hp : (1-J.matrix).PosDef) (L : ℕ) :
    (appendMinusOne J L).energy=J.energy+(L:ℝ)/4 := by
  have h := appendMinusOne_green J hp L
  unfold Jacobi.energy
  rw [← Equiv.sum_comp finSumFinEquiv (fun i => ((appendMinusOne J L).green i i)^2),Fintype.sum_sum_type]
  have hi (i : Fin N) : (appendMinusOne J L).green (Fin.castAdd L i) (Fin.castAdd L i)=J.green i i :=
    congrFun (congrFun h (Sum.inl i)) (Sum.inl i)
  have hj (j : Fin L) : (appendMinusOne J L).green (Fin.natAdd N j) (Fin.natAdd N j)=1/2 := by
    have he := congrFun (congrFun h (Sum.inr j)) (Sum.inr j)
    simpa using he
  simp only [finSumFinEquiv_apply_left,finSumFinEquiv_apply_right,hi,hj,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

end
end jacobi.Finite
