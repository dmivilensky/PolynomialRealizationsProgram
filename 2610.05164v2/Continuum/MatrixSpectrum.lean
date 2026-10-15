import «2610.05164v2».Continuum.AtomicSpectrum
import Mathlib.Analysis.Matrix.PosDef

/-!
Article: 2610.05164v2, Theorem 2.3.
The diagonal matrix's coordinate basis is another complete spectral basis.
Use: `«2610.05164v2».Continuum.diagonal_matrix_eigenvalue` feeds
`«2610.05164v2».Continuum.green_eigenvalue_eq` (The ordered spectrum extracted from the actual Green
matrix is the explicit finite sequence used in Theorem 2.4).
Proof chain: `«2610.05164v2».Packing.packed_spectral_distance` — 2610.05164v2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
-/
namespace «2610.05164v2».Continuum
noncomputable section
open Real
open scoped InnerProductSpace BigOperators Classical
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/--
Exact identity `DA.eigenvalue = DB.eigenvalue`.

Use: `«2610.05164v2».Packing.Jacobi.packing_spectral_distance` uses this identity to establish
the stated quantitative bound `(∑' j, |kernelEigenvalue (blocks J hN ht
hir).closedDensity_integrable (blocks J hN ht hir).closedDensity_nonneg j - finiteEigenvalue N
j|) ≤ 2/sqrt (N : ℝ)`.

Article: 2610.05164v2, Theorem 2.3.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.eigenvalue_basis_independent`
with the arguments shown in the proof.
-/
theorem eigenvalue_eq_of_operator_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {A B : E →L[ℝ] E} (h : A = B)
    (DA : PositiveSpectralData A) (DB : PositiveSpectralData B) : DA.eigenvalue = DB.eigenvalue := by
  subst B
  exact eigenvalue_basis_independent DA DB

/--
Finite matrix spectral data uses mathlib's orthonormal eigenvector basis.

Use: `«2610.05164v2».Continuum.diagonal_matrix_eigenvalue` uses this definition to establish
exact identity `(matrixSpectralData (Matrix.diagonal a) (Matrix.posSemidef_diagonal_iff.mpr
ha)).eigenvalue = spectralSorted (Summable.of_finite (f := a))`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.
-/
def matrixSpectralData (A : Matrix ι ι ℝ) (hA : A.PosSemidef) :
    PositiveSpectralData (Matrix.toEuclideanCLM (𝕜 := ℝ) A) where
  Index := ι
  basis := hA.isHermitian.eigenvectorBasis.toHilbertBasis
  eig := hA.isHermitian.eigenvalues
  equation i := by
    change (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) A).toLinearMap _ = _
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    simp only [OrthonormalBasis.coe_toHilbertBasis]
    apply PiLp.ext
    intro j
    change A.mulVec (hA.isHermitian.eigenvectorBasis i).ofLp j =
      hA.isHermitian.eigenvalues i * (hA.isHermitian.eigenvectorBasis i).ofLp j
    exact congrFun (hA.isHermitian.mulVec_eigenvectorBasis i) j
  nonneg := hA.eigenvalues_nonneg
  summable := Summable.of_finite

/--
Equal characteristic polynomials of positive matrices give equal sorted spectra.

Exact identity `(matrixSpectralData A hA).eigenvalue = (matrixSpectralData B hB).eigenvalue`.

Use: `«2610.05164v2».Continuum.green_eigenvalue_eq` rewrites with this identity to establish
exact identity `(greenSpectralData J hN ht).eigenvalue = finiteEigenvalue N`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem matrix_eigenvalue_eq_of_charpoly (A B : Matrix ι ι ℝ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (h : A.charpoly = B.charpoly) : (matrixSpectralData A hA).eigenvalue = (matrixSpectralData B hB).eigenvalue := by
  have he := (hA.isHermitian.eigenvalues_eq_eigenvalues_iff hB.isHermitian).mpr h
  change spectralSorted (Summable.of_finite (f := hA.isHermitian.eigenvalues)) =
    spectralSorted (Summable.of_finite (f := hB.isHermitian.eigenvalues))
  exact congrArg (fun a : ι → ℝ => spectralSorted (Summable.of_finite (f := a))) he

/--
The diagonal matrix's coordinate basis is another complete spectral basis.

Use: `«2610.05164v2».Continuum.diagonal_matrix_eigenvalue` uses this definition to establish
exact identity `(matrixSpectralData (Matrix.diagonal a) (Matrix.posSemidef_diagonal_iff.mpr
ha)).eigenvalue = spectralSorted (Summable.of_finite (f := a))`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.
-/
def diagonalMatrixSpectralData (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    PositiveSpectralData (Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.diagonal a)) where
  Index := ι
  basis := (EuclideanSpace.basisFun ι ℝ).toHilbertBasis
  eig := a
  equation i := by
    change (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) (Matrix.diagonal a)).toLinearMap _ = _
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    simp only [OrthonormalBasis.coe_toHilbertBasis]
    apply PiLp.ext
    intro j
    change (Matrix.diagonal a).mulVec ((EuclideanSpace.basisFun ι ℝ i).ofLp) j =
      a i * (EuclideanSpace.basisFun ι ℝ i).ofLp j
    simp only [Matrix.mulVec_diagonal]
    by_cases h : j=i
    · subst j; rfl
    · simp [EuclideanSpace.basisFun_apply,h]
  nonneg := ha
  summable := Summable.of_finite

/--
Exact identity `(matrixSpectralData (Matrix.diagonal a) (Matrix.posSemidef_diagonal_iff.mpr
ha)).eigenvalue = spectralSorted (Summable.of_finite (f := a))`.

Use: `«2610.05164v2».Continuum.green_eigenvalue_eq` rewrites with this identity to establish
exact identity `(greenSpectralData J hN ht).eigenvalue = finiteEigenvalue N`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.eigenvalue_basis_independent`
with the arguments shown in the proof.
-/
theorem diagonal_matrix_eigenvalue (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (matrixSpectralData (Matrix.diagonal a) (Matrix.posSemidef_diagonal_iff.mpr ha)).eigenvalue =
      spectralSorted (Summable.of_finite (f := a)) :=
  eigenvalue_basis_independent _ (diagonalMatrixSpectralData a ha)

end
end «2610.05164v2».Continuum
