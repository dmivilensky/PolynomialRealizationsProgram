import jacobi.Finite.ClosedSpectralApproximation

/-!
The common Green spectrum of a closed polynomial fibre, with multiplicities.
The diagonal chain supplies a concrete member even for repeated roots.
The finite spectral theorem then shows that every member has the same
normalized resolvent characteristic polynomial and the same sorted spectrum.
Use: ClosedTransfer states its hypothesis on the prescribed fibre, rather
than on an unspecified choice of matrices or eigenvectors.
Article: jacobi, Lemma 5.2.
Article role: continuity and contractive approximation in the closed-fibre transfer proof.
-/
namespace jacobi.Finite
noncomputable section
open chebyshev1 chebyshev2 chebyshev2.Continuum Matrix Polynomial
set_option backward.isDefEq.respectTransparency false

/-- The completely restarted chain with precisely the given roots.
It witnesses nonemptiness of every closed fibre, including repeated roots.
Article: jacobi, Lemma 5.2.
-/
def ClosedNodes.diagonalChain {N : ℕ} (S : ClosedNodes N) : Jacobi N where
  data := { b := fun i => if h : i<N then S.value ⟨i,h⟩ else 0
            aSq := fun _ => 0 }
  coupling_nonneg _ := le_refl 0
  coupling_zero := rfl
  diagonal_tail _ hi := dite_eq_right (not_lt.mpr hi)
  coupling_tail _ _ := rfl

/-- The coefficient encoding of the fully restarted chain is the literal
diagonal matrix of roots, without any simplicity requirement.
Article: jacobi, Lemma 5.2.
-/
theorem ClosedNodes.diagonalChain_matrix {N : ℕ} (S : ClosedNodes N) :
    S.diagonalChain.matrix=diagonal S.value := by
  ext i j
  simp only [Jacobi.matrix,JacobiData.matrix_apply,Nat.zero_add,
    ClosedNodes.diagonalChain,Matrix.diagonal_apply,Real.sqrt_zero]
  split_ifs <;> simp_all

/-- The fully restarted chain belongs to the prescribed closed fibre.
Article: jacobi, Lemma 5.2.
-/
theorem ClosedNodes.diagonalChain_mem {N : ℕ} (S : ClosedNodes N) :
    InClosedFiber S.diagonalChain S.polynomial := by
  change S.diagonalChain.matrix.charpoly=S.polynomial
  rw [S.diagonalChain_matrix,Matrix.charpoly_diagonal]
  rfl

/-- Diagonalization of the actual normalized Green matrix in the original
matrix's canonical spectral coordinates. Multiplicities require no choices.
Article: jacobi, Lemma 5.2.
-/
theorem ClosedNodes.green_charpoly {N : ℕ} (S : ClosedNodes N) {J : Jacobi N}
    (hJ : InClosedFiber J S.polynomial) :
    J.normalizedGreen.charpoly=∏ i:Fin N,
      (X-C ((1-J.matrix_isHermitian.eigenvalues i)⁻¹/(N:ℝ)^2)) := by
  let B := SpectralBasis.ofHermitian J.matrix J.matrix_isHermitian
  have hn (i : Fin N) : 1-B.eigenvalues i≠0 := by
    have hi := J.matrix_isHermitian.eigenvalues_mem_spectrum_real i
    rw [S.spectrum_eq hJ] at hi
    obtain ⟨k,hk⟩ := hi
    change 1-J.matrix_isHermitian.eigenvalues i≠0
    rw [← hk]
    exact (sub_pos.mpr (S.interval k).2).ne'
  rw [← SpectralCoordinates.ofHermitian_charpoly J.matrix_isHermitian J.normalizedGreen]
  change (B.Qᵀ*J.normalizedGreen*B.Q).charpoly=_
  rw [Jacobi.normalizedGreen,Matrix.mul_smul,Matrix.smul_mul]
  change (((N:ℝ)^2)⁻¹ • B.coordinates J.green).charpoly=_
  rw [Jacobi.green,SpectralCoordinates.coordinates_resolvent B hn,← Matrix.diagonal_smul,
    Matrix.charpoly_diagonal]
  simp only [Pi.smul_apply,smul_eq_mul,B,SpectralBasis.ofHermitian,div_eq_mul_inv,mul_comm]

/-- All closed-fibre members have the same actual sorted normalized Green
spectrum. This includes every multiplicity and every arrangement of blocks.
Article: jacobi, Lemma 5.2.
-/
theorem ClosedNodes.spectrum_independent {N : ℕ} (S : ClosedNodes N)
    {J K : Jacobi N} (hJ : InClosedFiber J S.polynomial)
    (hK : InClosedFiber K S.polynomial) :
    closedSpectrum J (S.endpoint_posDef hJ)=closedSpectrum K (S.endpoint_posDef hK) := by
  have he := (J.matrix_isHermitian.eigenvalues_eq_eigenvalues_iff
    K.matrix_isHermitian).mpr (hJ.trans hK.symm)
  apply matrix_eigenvalue_eq_of_charpoly
  rw [S.green_charpoly hJ,S.green_charpoly hK,he]

/-- The common normalized Green spectrum of the entire closed fibre.
Its concrete diagonal representative makes the definition independent of
existence, minimizer or irreducibility premises.
Article: jacobi, Lemma 5.2.
-/
def closedFibreSpectrum {N : ℕ} (S : ClosedNodes N) : ℕ → ℝ :=
  closedSpectrum S.diagonalChain (S.endpoint_posDef S.diagonalChain_mem)

/-- Every member realizes exactly the fibre's common spectral sequence.
Article: jacobi, Lemma 5.2.
-/
theorem ClosedNodes.closedSpectrum_eq {N : ℕ} (S : ClosedNodes N) {J : Jacobi N}
    (hJ : InClosedFiber J S.polynomial) :
    closedSpectrum J (S.endpoint_posDef hJ)=closedFibreSpectrum S :=
  S.spectrum_independent hJ S.diagonalChain_mem

end
end jacobi.Finite
