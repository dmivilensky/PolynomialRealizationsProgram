import krylov.Reference.GradientMeasure
import krylov.Reference.Lanczos
import krylov.LinearAlgebra.MatrixEquiv

/-!
Article: main_krylov, Section 2, prop:dict(i) and s5:fibre, actual positive Lanczos orientation.
Use: construct the orthonormal Lanczos vectors of the actual matrix and initial
gradient from the existing canonical orthogonal-polynomial construction.
Source: finite Lanczos--Stieltjes reconstruction (Meurant06, GolubMeurant10),
reusing jacobi's genuine measure, polynomial basis and Jacobi coefficients.
-/

namespace krylov.Reference
noncomputable section
open Matrix Polynomial jacobi.Finite
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
variable {n : ℕ}

/-- Actual positively oriented Lanczos vectors, constructed from the actual gradient measure's canonical polynomials.
Use: fixes the positive-off-diagonal convention in the source's information fibre.
Article: main_krylov, s5:fibre, Z=[z₀,...,z_(N−1)]. -/
def lanczosVector (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hg : g≠0) (i : Fin (activeSpectralValues base hb.1 g).card) :
    EuclideanSpace ℝ (Fin n) :=
  ‖g‖⁻¹ • CG.polynomialAction (cgOperator base) g ((gradientSpectralData base hb g hg).orthogonalPolynomial i)

/-- The actual measure-constructed Lanczos vectors are orthonormal in the original physical space.
Use: the source's matrix Z is a genuine orthonormal reference frame, even when the ambient dimension exceeds its active support.
Article: main_krylov, s5:fibre, actual Lanczos orthogonality.
Proof: use the proved physical/gradient-measure inner-product identity and
the existing actual orthonormal polynomial basis, canceling only the nonzero initial norm. -/
theorem lanczosVector_orthonormal (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hg : g≠0) :
    Orthonormal ℝ (lanczosVector base hb g hg) := by
  -- Spectral reconstruction is transported isometrically into the actual original cyclic subspace.
  rw [orthonormal_iff_ite]
  intro i j
  rw [lanczosVector, lanczosVector, real_inner_smul_left, real_inner_smul_right,
    gradientSpectralData_inner base hb g hg,
    (gradientSpectralData base hb g hg).evaluate_orthogonalPolynomial,
    (gradientSpectralData base hb g hg).evaluate_orthogonalPolynomial,
    (gradientSpectralData base hb g hg).polynomialBasis.inner_eq_ite]
  have hn := norm_ne_zero_iff.mpr hg
  split_ifs <;> field_simp

/-- The constructed physical Lanczos process starts with the actual normalized initial gradient.
Use: identifies its first-site spectral data as the paper's prescribed gradient measure.
Article: main_krylov, s5:fibre, z₀=g₀/‖g₀‖.
Proof: the actual probability measure's first orthogonal polynomial is the constant one. -/
theorem lanczosVector_first (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hg : g≠0) :
    lanczosVector base hb g hg ⟨0, support_pos (gradientSpectralData base hb g hg)⟩=‖g‖⁻¹ • g := by
  rw [lanczosVector, orthogonalPolynomial_first]
  simp only [CG.polynomialAction, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_one,
    ContinuousLinearMap.coe_coe, ContinuousLinearMap.apply_apply, one_apply_eq_self]

/-- The reconstructed gradient-measure Jacobi matrix is exactly the physical operator compression in the actual constructed Lanczos vectors.
Use: closes the matrix/measure/trajectory dictionary with the original physical operator.
Article: main_krylov, s5:fibre, J=ZᵀAZ, positive off-diagonal orientation.
Proof: multiplication by X is the actual operator action; the proved spectral
inner-product identity turns its physical compression into the reused multiplication matrix. -/
theorem lanczosVector_compression (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hg : g≠0) (i j : Fin (activeSpectralValues base hb.1 g).card) :
    inner ℝ (lanczosVector base hb g hg i) (cgOperator base (lanczosVector base hb g hg j))=
      (gradientSpectralData base hb g hg).reconstructed.matrix i j := by
  -- Both the original matrix action and the reconstructed Jacobi entry use the same actual polynomial integral.
  let M := gradientSpectralData base hb g hg
  have hx : cgOperator base (CG.polynomialAction (cgOperator base) g (M.orthogonalPolynomial j))=
      CG.polynomialAction (cgOperator base) g (X*M.orthogonalPolynomial j) := by
    simp only [CG.polynomialAction, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      ContinuousLinearMap.coe_coe, ContinuousLinearMap.apply_apply, map_mul, aeval_X, mul_apply_eq_comp]
  rw [lanczosVector, lanczosVector, map_smul, real_inner_smul_left, real_inner_smul_right,
    hx, gradientSpectralData_inner base hb g hg, M.reconstructed_matrix]
  change ‖g‖⁻¹*(‖g‖⁻¹*(‖g‖^2*inner ℝ (M.evaluate (M.orthogonalPolynomial i))
    (M.evaluate (X*M.orthogonalPolynomial j))))=M.multiplication i j
  rw [M.evaluate_orthogonalPolynomial]
  change ‖g‖⁻¹*(‖g‖⁻¹*(‖g‖^2*M.multiplication i j))=M.multiplication i j
  field_simp [norm_ne_zero_iff.mpr hg]

/-- The actual positively oriented Lanczos compression has strictly positive adjacent couplings.
Use: source irreducibility follows from the constructed measure rather than an assumed Jacobi representation.
Article: main_krylov, s5:fibre, J_(k,k+1)>0.
Proof: the compression is the actual reconstructed multiplication matrix, whose positive adjacent entries were proved in jacobi. -/
theorem lanczosVector_adjacent_pos (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hg : g≠0) (i j : Fin (activeSpectralValues base hb.1 g).card)
    (hij : i.val+1=j.val) :
    0 < inner ℝ (lanczosVector base hb g hg i) (cgOperator base (lanczosVector base hb g hg j)) := by
  rw [lanczosVector_compression, (gradientSpectralData base hb g hg).reconstructed_matrix]
  exact (gradientSpectralData base hb g hg).multiplication_adjacent_pos i j hij

/-- The actual measure-constructed Lanczos compression is positive definite in the original physical metric.
Use: its Gaussian quadrature nodes and inverse moments belong to a genuine positive reference compression.
Article: main_krylov, s5:fibre, positive Jacobi compression.
Proof: its actual matrix is the Gram matrix of the positive-root images of
the actual orthonormal Lanczos vectors; the true root equivalence preserves independence. -/
theorem lanczosVector_compression_posDef (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hg : g≠0) :
    (gradientSpectralData base hb g hg).reconstructed.matrix.PosDef := by
  -- This positive Gram realization uses the actual physical metric root, not an assumed spectral lower bound for the reconstruction.
  let R := krylov.LinearAlgebra.matrixEquiv (krylov.Secant.metricRoot base) (krylov.Secant.metricRoot_det_unit base hb)
  have hli := (lanczosVector_orthonormal base hb g hg).linearIndependent.map' R.toLinearMap
    (LinearMap.ker_eq_bot.mpr R.injective)
  have he : Matrix.gram ℝ (fun i => R (lanczosVector base hb g hg i))=
      (gradientSpectralData base hb g hg).reconstructed.matrix := by
    ext i j
    have hp := canonical_search_pairing base hb (lanczosVector base hb g hg i)
      (cgOperator base (lanczosVector base hb g hg j))
    rw [canonical_reference_action base hb] at hp
    exact hp.symm.trans (lanczosVector_compression base hb g hg i j)
  rw [← he]
  exact Matrix.posDef_gram_of_linearIndependent hli

end
end krylov.Reference
