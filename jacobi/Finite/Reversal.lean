import jacobi.Finite.Fiber

/-!
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Reversal preserves canonical finite Jacobi coefficients, the characteristic
polynomial and the energy, without imposing a special terminal polynomial.
Use: the fibre involution whose fixed point is the persymmetric realization.
-/

namespace jacobi.Finite
noncomputable section
open chebyshev1 chebyshev2 Matrix
open scoped BigOperators

variable {N : ℕ}

/-- Reverse the finite chain and retain its canonical zero extension.
Use: the fibre involution whose fixed point is the persymmetric realization.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
-/
def reverse (J : Jacobi N) : Jacobi N where
  data := {
    b := fun i => if i < N then J.data.b (N-1-i) else 0
    aSq := fun i => if 0 < i ∧ i < N then J.data.aSq (N-i) else 0 }
  coupling_nonneg i := by
    dsimp
    split_ifs
    · exact J.coupling_nonneg _
    · exact le_rfl
  coupling_zero := by simp
  diagonal_tail i hi := by simp [not_lt.mpr hi]
  coupling_tail i hi := by simp [not_lt.mpr hi]

/-- The constructed reverse is exactly simultaneous row and column reversal.
Use: transports inverse matrices and their spectral data.
Article: jacobi, Proposition 1.1.
Proof: compare with the existing reversed continuant matrix entry by entry. -/
theorem reverse_matrix (J : Jacobi N) :
    (reverse J).matrix = J.matrix.submatrix Fin.rev Fin.rev := by
  -- Compare the canonical reversed coefficients with the existing reversed continuant matrix entry by entry.
  calc
    (reverse J).matrix = (J.data.reversed N).matrix 0 N := by
      ext i j
      have hi := i.isLt
      have hj := j.isLt
      simp only [Jacobi.matrix, JacobiData.matrix_apply, reverse, Nat.zero_add]
      split_ifs <;> simp_all [JacobiData.reversed]
    _ = J.matrix.submatrix Fin.rev Fin.rev := by
      simpa only [Nat.sub_zero, Nat.sub_self, Jacobi.matrix]
        using J.data.reversed_matrix N 0 N (by omega)

/-- Reversal preserves the monic terminal polynomial.
Use: proves that reversal acts inside every fibre.
Article: jacobi, Proposition 1.1.
Proof: characteristic polynomials are invariant under permutation conjugation. -/
theorem reverse_charpoly (J : Jacobi N) : (reverse J).matrix.charpoly = J.matrix.charpoly := by
  rw [reverse_matrix]
  exact Matrix.charpoly_reindex Fin.revPerm J.matrix

/-- Positive internal couplings remain positive after reversal.
Use: reversal preserves the irreducible fibre rather than only its closure.
Article: jacobi, Proposition 1.1.
Proof: the internal edge i corresponds to the internal edge N − i. -/
theorem reverse_irreducible (J : Jacobi N) (hJ : J.Irreducible) : (reverse J).Irreducible := by
  intro i hi hiN
  change 0 < if 0 < i ∧ i < N then J.data.aSq (N-i) else 0
  rw [ite_eq_left ⟨hi, hiN⟩]
  exact hJ (N-i) (by omega) (by omega)

/-- Reversal acts in every monic fibre.
Use: is the finite involution underlying the logarithmic weight coordinates.
Article: jacobi, Proposition 1.1.
Proof: combine preservation of the couplings and characteristic polynomial. -/
theorem reverse_mem_fiber {J : Jacobi N} {p : Polynomial ℝ} (hJ : InFiber J p) :
    InFiber (reverse J) p :=
  ⟨reverse_irreducible J hJ.1, (reverse_charpoly J).trans hJ.2⟩

/-- Green matrices reverse with the same row and column permutation.
Use: transfers the resolvent diagonal and proves energy invariance.
Article: jacobi, Proposition 1.1.
Proof: nonsingular matrix inverse commutes with simultaneous reindexing. -/
theorem reverse_green (J : Jacobi N) :
    (reverse J).green = J.green.submatrix Fin.rev Fin.rev := by
  unfold Jacobi.green
  rw [reverse_matrix]
  have h : 1 - J.matrix.submatrix Fin.rev Fin.rev =
      (1-J.matrix).submatrix Fin.rev Fin.rev := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.one_apply, Fin.rev_injective.eq_iff]
  rw [h]
  exact Matrix.inv_submatrix_equiv _ Fin.revPerm Fin.revPerm

/-- Energy is invariant under reversal for every finite chain.
Use: yields evenness after the spectral weights are written in logarithmic coordinates.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: the reversed Green diagonal merely permutes the summands. -/
theorem reverse_energy (J : Jacobi N) : (reverse J).energy = J.energy := by
  simp only [Jacobi.energy, reverse_green, Matrix.submatrix_apply]
  exact Equiv.sum_comp Fin.revPerm (fun i => J.green i i^2)

/-- Reversing twice recovers the canonical finite coefficient record itself.
Use: supplies an actual involution on the arbitrary fibre, not just matrix equality.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: internal indices reverse twice; the prescribed zero tails handle all remaining indices. -/
theorem reverse_involution (J : Jacobi N) : reverse (reverse J) = J := by
  -- Internal indices reverse twice; canonical zero tails determine all indices outside the finite matrix.
  have hd (D E : JacobiData) (hb : D.b = E.b) (ha : D.aSq = E.aSq) : D = E := by
    cases D
    cases E
    simp_all
  apply Jacobi.ext
  apply hd
  · funext i
    by_cases hi : i < N
    · have hi' : N-1-i < N := by omega
      have he : N-1-(N-1-i) = i := by omega
      simp [reverse, hi, hi', he]
    · simp [reverse, hi, J.diagonal_tail i (le_of_not_gt hi)]
  · funext i
    by_cases hi : 0 < i ∧ i < N
    · have hi' : 0 < N-i ∧ N-i < N := by omega
      have he : N-(N-i) = i := by omega
      change (if 0 < i ∧ i < N then
        (if 0 < N-i ∧ N-i < N then J.data.aSq (N-(N-i)) else 0) else 0) = J.data.aSq i
      rw [ite_eq_left hi, ite_eq_left hi', he]
    · have hz : J.data.aSq i = 0 := by
        by_cases hi0 : i = 0
        · simpa [hi0] using J.coupling_zero
        · exact J.coupling_tail i (by omega)
      simp [reverse, hi, hz]

/-- A reversal-fixed matrix has a symmetric resolvent diagonal.
Use: extends the half-chain eigenvector and diagonal limits to the entire interval.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
Proof: its Green matrix is reversal-fixed by invariance of inverse under reindexing. -/
theorem green_diagonal_symmetric (J : Jacobi N)
    (hJ : J.matrix.submatrix Fin.rev Fin.rev = J.matrix) (i : Fin N) :
    J.green i.rev i.rev = J.green i i := by
  have he : (reverse J).green = J.green := by
    unfold Jacobi.green
    rw [reverse_matrix, hJ]
  rw [reverse_green] at he
  exact congrArg (fun A : Matrix (Fin N) (Fin N) ℝ => A i i) he

end
end jacobi.Finite
