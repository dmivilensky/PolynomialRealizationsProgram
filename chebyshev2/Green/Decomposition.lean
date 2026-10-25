import chebyshev2.Green.Compression

/-!
Article: chebyshev2, Theorem A.1.
Recovering the odd/even bidiagonal block of a centered chain.
Use: `chebyshev2.Centering.charpoly_compression` feeds
`chebyshev2.Centering.compression_terminal` (compression terminal).
Proof chain: `chebyshev2.centeringEquiv` — chebyshev2, Theorem A.1; Centering lift,
contractivity, odd Green entries and characteristic polynomial.
-/
namespace chebyshev2.Centering
noncomputable section
open chebyshev1 Matrix
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} (C : Jacobi (2*N))

/--
Recovering the odd/even bidiagonal block of a centered chain.

Exact identity `C.matrix.submatrix (interleave N) (interleave N) = blockLift (extractedBlock
C)`.

Use: `chebyshev2.Centering.charpoly_compression` rewrites with this identity to establish
exact identity `C.matrix.charpoly = Polynomial.C ((1/2:ℝ)^N)*(compression
C).matrix.charpoly.comp (2*Polynomial.X^2-1)`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.centeringEquiv`.

Proof: Separate `n < 2*N` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem grouped_matrix (hc : C.Centered) :
    C.matrix.submatrix (interleave N) (interleave N) = blockLift (extractedBlock C) := by
  -- Separate `n < 2*N` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  have hd (n : ℕ) : C.data.b n = 0 := by
    by_cases hn : n < 2*N
    · exact hc.2 n hn
    · exact C.diagonal_tail n (by omega)
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have ha : ¬2*i.val+1 = 2*j.val := by omega
      have hb : ¬2*j.val+1 = 2*i.val := by omega
      simp [Matrix.submatrix, Jacobi.matrix, JacobiData.matrix_apply, blockLift,
        interleave_left, hd, ha, hb]
    | inr j =>
      have he : interleave N (Sum.inl i) ≠ interleave N (Sum.inr j) :=
        (interleave N).injective.ne (by simp)
      have ha : 2*i.val+1 = 2*j.val+1 ↔ i = j := by rw [Fin.ext_iff]; omega
      have hb : 2*j.val+1+1 = 2*i.val ↔ j.val+1 = i.val := by omega
      simp only [Matrix.submatrix_apply, Jacobi.matrix, JacobiData.matrix_apply, Nat.zero_add,
        he, ite_false, interleave_left, interleave_right, blockLift, Matrix.fromBlocks_apply₁₂,
        ha, hb, extractedBlock, Bidiagonal.matrix, diagonal, lower]
      by_cases hij : i = j
      · subst j; simp
      · simp [hij]
  | inr i =>
    cases j with
    | inl j =>
      have he : interleave N (Sum.inr i) ≠ interleave N (Sum.inl j) :=
        (interleave N).injective.ne (by simp)
      have ha : 2*i.val+1+1 = 2*j.val ↔ i.val+1 = j.val := by omega
      have hb : 2*j.val+1 = 2*i.val+1 ↔ j = i := by rw [Fin.ext_iff]; omega
      simp only [Matrix.submatrix_apply, Jacobi.matrix, JacobiData.matrix_apply, Nat.zero_add,
        he, ite_false, interleave_left, interleave_right, blockLift, Matrix.fromBlocks_apply₂₁,
        Matrix.transpose_apply, ha, hb, extractedBlock, Bidiagonal.matrix, diagonal, lower]
      by_cases hij : j = i
      · subst j; simp
      · simp only [hij,ite_false]
        simp only [zero_add]
    | inr j =>
      have ha : ¬2*i.val+1 = 2*j.val := by omega
      have hb : ¬2*j.val+1 = 2*i.val := by omega
      simp [Matrix.submatrix, Jacobi.matrix, JacobiData.matrix_apply, blockLift,
        interleave_right, hd, ha, hb]

/--
Exact identity `C.matrix.charpoly = Polynomial.C ((1/2:ℝ)^N)*(compression
C).matrix.charpoly.comp (2*Polynomial.X^2-1)`.

Use: `chebyshev2.Centering.compression_terminal` rewrites with this identity to establish
the precise assertion is `(compression C).Terminal`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.centeringEquiv`.

Proof: Use the identities/estimates `chebyshev2.Centering.grouped_matrix`,
`chebyshev2.Centering.blockLift_affine_charpoly`,
`chebyshev2.Centering.compression_matrix` with the arguments shown in the proof.
-/
theorem charpoly_compression (hc : C.Centered) : C.matrix.charpoly =
    Polynomial.C ((1/2:ℝ)^N)*(compression C).matrix.charpoly.comp (2*Polynomial.X^2-1) := by
  have he := Matrix.charpoly_reindex (interleave N).symm C.matrix
  change (C.matrix.submatrix (interleave N) (interleave N)).charpoly = C.matrix.charpoly at he
  rw [← he, grouped_matrix C hc, blockLift_affine_charpoly, ← compression_matrix C]

end
end chebyshev2.Centering
