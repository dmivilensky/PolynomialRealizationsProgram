import bezout.Gains.Matrix
import Mathlib.Analysis.Matrix.Spectrum

/-!
Article: bezout, Theorem 4.1, matrix and abstract Hilbert-space comparison classes.
Use: the real symmetric matrix model and its actual Euclidean linear action
have exactly the same admissible spectral domain.
Proof: finite-dimensional eigenvalues coincide with the endomorphism spectrum,
and Euclidean matrix representation preserves both spectrum and symmetry.
-/

namespace bezout.Analysis
noncomputable section

/-- The eigenvalue formulation of admissibility is exactly the spectral formulation.
Use: compares the actual-execution Hilbert model with the article's matrix class. -/
theorem admissible_iff_spectrum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (I : chebyshev1.SpectralInterval) (H : E →ₗ[ℝ] E) :
    Admissible I H ↔ H.IsSymmetric ∧ spectrum ℝ H ⊆ Set.Icc I.mu I.L := by
  constructor
  · rintro ⟨hH, he⟩
    exact ⟨hH, fun x hx => he x (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hx)⟩
  · rintro ⟨hH, hs⟩
    exact ⟨hH, fun x hx => hs (Module.End.hasEigenvalue_iff_mem_spectrum.mp hx)⟩

end
end bezout.Analysis

namespace bezout.History
noncomputable section
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The actual matrix action equals the standard Euclidean linear representation.
Use: transfers matrix symmetry and spectrum to the physical oracle Hessian. -/
theorem matrixEnd_eq_toEuclideanLin (H : Matrix d d ℝ) :
    matrixEnd H = Matrix.toEuclideanLin H := rfl

/-- Matrix admissibility is exactly admissibility of its actual Euclidean action.
Use: closes the semantic dictionary for the universal Hilbert--Schmidt gains. -/
theorem matrixEnd_admissible_iff (I : chebyshev1.SpectralInterval) (H : Matrix d d ℝ) :
    bezout.Analysis.Admissible I (matrixEnd H) ↔
      H.IsHermitian ∧ spectrum ℝ H ⊆ Set.Icc I.mu I.L := by
  rw [bezout.Analysis.admissible_iff_spectrum, matrixEnd_eq_toEuclideanLin,
    Matrix.isSymmetric_toEuclideanLin_iff, Matrix.spectrum_toLpLin]

/-- Every admissible real symmetric matrix is an admissible actual physical Hessian.
Use: matrix witnesses and matrix upper bounds quantify literal oracle executions. -/
theorem matrixEnd_admissible (I : chebyshev1.SpectralInterval) (H : Matrix d d ℝ)
    (hH : H.IsHermitian) (hs : spectrum ℝ H ⊆ Set.Icc I.mu I.L) :
    bezout.Analysis.Admissible I (matrixEnd H) :=
  (matrixEnd_admissible_iff I H).mpr ⟨hH, hs⟩

end
end bezout.History
