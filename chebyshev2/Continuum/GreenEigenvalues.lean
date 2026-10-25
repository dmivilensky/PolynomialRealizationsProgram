import chebyshev2.Continuum.MatrixSpectrum
import chebyshev2.Continuum.FiniteSorting
import chebyshev2.Continuum.ReferenceSpectrum

/-!
Article: chebyshev2, Theorem 2.3.
The ordered spectrum extracted from the actual Green matrix is the explicit finite sequence used in
Theorem 2.4.
Use: `chebyshev2.Continuum.green_eigenvalue_eq` feeds
`chebyshev2.Packing.packed_spectral_distance` (Theorem 2.3, equation (7), for the full fiber
including zero edges).
Proof chain: `chebyshev2.Packing.packed_spectral_distance` — chebyshev2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
-/
namespace chebyshev2.Continuum
noncomputable section
open Real
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

variable {N : ℕ} (J : chebyshev2.Jacobi N)

/--
The precise assertion is `J.normalizedGreen.PosSemidef`.

Use: `chebyshev2.Continuum.greenSpectralData` uses this assertion in the displayed
construction of `greenSpectralData`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Use the identities/estimates `chebyshev2.Jacobi.one_sub_posDef` with the arguments
shown in the proof.
-/
theorem normalizedGreen_posSemidef (hN : 0 < N) (ht : J.Terminal) : J.normalizedGreen.PosSemidef :=
  (J.one_sub_posDef hN ht).inv.posSemidef.smul (by positivity)

/--
Defines `greenSpectralData` of type `PositiveSpectralData (Matrix.toEuclideanCLM (𝕜 := ℝ)
J.normalizedGreen)` by `matrixSpectralData _ (normalizedGreen_posSemidef J hN ht)`.

Use: `chebyshev2.Continuum.green_eigenvalue_eq` uses this definition to establish exact
identity `(greenSpectralData J hN ht).eigenvalue = finiteEigenvalue N`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.
-/
def greenSpectralData (hN : 0 < N) (ht : J.Terminal) :
    PositiveSpectralData (Matrix.toEuclideanCLM (𝕜 := ℝ) J.normalizedGreen) :=
  matrixSpectralData _ (normalizedGreen_posSemidef J hN ht)

/--
The ordered spectrum extracted from the actual Green matrix is the explicit finite sequence
used in Theorem 2.4.

Exact identity `(greenSpectralData J hN ht).eigenvalue = finiteEigenvalue N`.

Use: `chebyshev2.Packing.Jacobi.packing_spectral_distance` uses this identity to establish
the stated quantitative bound `(∑' j, |kernelEigenvalue (blocks J hN ht
hir).closedDensity_integrable (blocks J hN ht hir).closedDensity_nonneg j - finiteEigenvalue N
j|) ≤ 2/sqrt (N : ℝ)`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem green_eigenvalue_eq (hN : 0 < N) (ht : J.Terminal) :
    (greenSpectralData J hN ht).eigenvalue = finiteEigenvalue N := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  let a : Fin N → ℝ := chebyshev2.Jacobi.normalizedGreenValue N
  have hp (i : Fin N) : 0 < a i := by
    change 0 < chebyshev2.Jacobi.normalizedGreenValue N i
    have h := (referenceEigenvalue_pos i.val).trans_le (finiteEigenvalue_bounds i.isLt).1
    simpa only [finiteEigenvalue,dite_eq_left i.isLt] using h
  have hn (i : Fin N) : 0 ≤ a i := (hp i).le
  have he : J.normalizedGreen.charpoly = (Matrix.diagonal a).charpoly := by
    rw [J.normalizedGreen_charpoly hN ht,Matrix.charpoly_diagonal]
  change (matrixSpectralData J.normalizedGreen _).eigenvalue = _
  rw [matrix_eigenvalue_eq_of_charpoly _ _ (normalizedGreen_posSemidef J hN ht)
    (Matrix.posSemidef_diagonal_iff.mpr hn) he,diagonal_matrix_eigenvalue a hn]
  funext n
  exact spectralSorted_fin (chebyshev2.Jacobi.normalizedGreenValue_strictAnti N) hp Summable.of_finite n

end
end chebyshev2.Continuum
