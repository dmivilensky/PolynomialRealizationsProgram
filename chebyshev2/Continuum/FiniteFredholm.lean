import chebyshev2.Continuum.SpectralFunctional
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
Article: chebyshev2, Proposition 3.
Finite-rank synthesis may have a kernel.
Use: `chebyshev2.Continuum.familyGram_logDeterminant_of_eq` feeds
`chebyshev2.Continuum.finite_rankOne_logDeterminant` (Logarithmic determinant update in finite
rank).
Proof chain: `chebyshev2.Comparison.Profile.signed_determinant_comparison` — chebyshev2,
Theorem 3.4; Signed determinant and square-trace comparisons.
-/
namespace chebyshev2.Continuum
noncomputable section
open Real Matrix Unitary
open scoped InnerProductSpace BigOperators Classical
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/--
Exact identity `(1+a • A).det = ∏ i, (1+a*hA.eigenvalues i)`.

Use: `chebyshev2.Continuum.matrix_logDeterminant` rewrites with this identity to establish
exact identity `logDeterminant (matrixSpectralData A hA).eigenvalue s = log (1+(s/2) • A).det`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem matrix_det_pencil (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (a : ℝ) :
    (1+a • A).det = ∏ i, (1+a*hA.eigenvalues i) := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  let U := conjStarAlgAut ℝ _ hA.eigenvectorUnitary
  have he : (1+a • A) = U (Matrix.diagonal (fun i => 1+a*hA.eigenvalues i)) := by
    rw [show Matrix.diagonal (fun i => 1+a*hA.eigenvalues i) =
        1+a • Matrix.diagonal hA.eigenvalues by
      rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, ← Matrix.diagonal_add]
      rfl]
    simp only [map_add,map_one,map_smul]
    congr 2
    exact hA.spectral_theorem
  rw [he]
  change ((↑hA.eigenvectorUnitary : Matrix ι ι ℝ) *
    Matrix.diagonal (fun i => 1+a*hA.eigenvalues i) *
    star (↑hA.eigenvectorUnitary : Matrix ι ι ℝ)).det = _
  rw [Matrix.det_mul,Matrix.det_mul]
  have hu : (↑hA.eigenvectorUnitary : Matrix ι ι ℝ).det *
      (star (↑hA.eigenvectorUnitary : Matrix ι ι ℝ)).det=1 := by
    rw [← Matrix.det_mul, ← coe_star, coe_mul_star_self,Matrix.det_one]
  rw [mul_right_comm,hu,one_mul,Matrix.det_diagonal]

/--
The literal finite determinant equals the same sorted spectral product used for the
infinite-dimensional Fredholm determinant.

Exact identity `logDeterminant (matrixSpectralData A hA).eigenvalue s = log (1+(s/2) • A).det`.

Use: `chebyshev2.Continuum.familyGram_logDeterminant` uses this identity to establish exact
identity `logDeterminant D.eigenvalue s = log (Matrix.det ((1 : Matrix ι ι ℝ)+(s/2) • Matrix.of
(fun i j => inner ℝ (v i) (v j))))`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Use the identities/estimates
`chebyshev2.Continuum.PositiveSpectralData.logDeterminant_eq`,
`chebyshev2.Continuum.matrix_det_pencil` with the arguments shown in the proof.
-/
theorem matrix_logDeterminant (A : Matrix ι ι ℝ) (hA : A.PosSemidef)
    {s : ℝ} (hs : 0 ≤ s) :
    logDeterminant (matrixSpectralData A hA).eigenvalue s = log (1+(s/2) • A).det := by
  -- Use the identities/estimates
  -- `chebyshev2.Continuum.PositiveSpectralData.logDeterminant_eq`,
  -- `chebyshev2.Continuum.matrix_det_pencil` with the arguments shown in the proof.
  rw [PositiveSpectralData.logDeterminant_eq _ hs]
  change (∑' i : ι, log (1+s/2*hA.isHermitian.eigenvalues i)) = _
  rw [tsum_fintype,matrix_det_pencil A hA.isHermitian]
  symm
  exact Real.log_prod (fun i _ => by
    have hi := hA.eigenvalues_nonneg i
    change 1+s/2*hA.isHermitian.eigenvalues i ≠ 0
    positivity)

omit [DecidableEq ι] in
/--
A Gram matrix of vectors in the actual feature space is positive.

The stated quantitative bound `Matrix.PosSemidef ((fun i j => inner ℝ (v i) (v j)) : Matrix ι ι
ℝ)`.

Use: `chebyshev2.Continuum.familyGram_logDeterminant` rewrites with this identity to
establish exact identity `logDeterminant D.eigenvalue s = log (Matrix.det ((1 : Matrix ι ι
ℝ)+(s/2) • Matrix.of (fun i j => inner ℝ (v i) (v j))))`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem familyGram_positive (v : ι → FeatureSpace) :
    Matrix.PosSemidef ((fun i j => inner ℝ (v i) (v j)) : Matrix ι ι ℝ) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    change inner ℝ (v j) (v i)=inner ℝ (v i) (v j)
    exact real_inner_comm _ _
  · intro z
    have h : z ⬝ᵥ ((fun i j => inner ℝ (v i) (v j)) *ᵥ z) =
        inner ℝ (∑ i, z i • v i) (∑ i, z i • v i) := by
      simp only [dotProduct, Matrix.mulVec, inner_sum, sum_inner,
        real_inner_smul_left,real_inner_smul_right,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [real_inner_comm (v i) (v j)]
      ring
    simpa only [star_trivial] using h ▸ (real_inner_self_nonneg (x := ∑ i, z i • v i))

/--
Finite-rank synthesis may have a kernel. The product still transfers exactly, using the
previously proved Gram multiplicity theorem.

Exact identity `logDeterminant D.eigenvalue s = log (Matrix.det ((1 : Matrix ι ι ℝ)+(s/2) •
Matrix.of (fun i j => inner ℝ (v i) (v j))))`.

Use: `chebyshev2.Continuum.familyGram_logDeterminant_of_eq` uses this identity to establish
exact identity `logDeterminant D.eigenvalue s = log (Matrix.det ((1 : Matrix ι ι ℝ)+(s/2) •
Matrix.of (fun i j => inner ℝ (v i) (v j))))`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Use the identities/estimates `chebyshev2.Continuum.familySynthesis_matrix`,
`chebyshev2.Continuum.gram_eigenvalue_eq`, `chebyshev2.Continuum.familyGram_positive`
with the arguments shown in the proof.
-/
theorem familyGram_logDeterminant (v : ι → FeatureSpace)
    (D : PositiveSpectralData (∑ i, InnerProductSpace.rankOne ℝ (v i) (v i)))
    {s : ℝ} (hs : 0 ≤ s) :
    logDeterminant D.eigenvalue s =
      log (Matrix.det ((1 : Matrix ι ι ℝ)+(s/2) •
        Matrix.of (fun i j => inner ℝ (v i) (v j)))) := by
  -- Use the identities/estimates `chebyshev2.Continuum.familySynthesis_matrix`,
  -- `chebyshev2.Continuum.gram_eigenvalue_eq`,
  -- `chebyshev2.Continuum.familyGram_positive` with the arguments shown in the proof.
  let M : Matrix ι ι ℝ := fun i j => inner ℝ (v i) (v j)
  have he : Matrix.toEuclideanCLM (𝕜 := ℝ) M =
      (familySynthesis v).adjoint ∘L familySynthesis v := by
    apply ContinuousLinearMap.coe_injective
    change Matrix.toEuclideanLin M = _
    dsimp only [M]
    rw [← familySynthesis_matrix v]
    exact (LinearMap.toMatrix (EuclideanSpace.basisFun ι ℝ).toBasis
      (EuclideanSpace.basisFun ι ℝ).toBasis).symm_apply_apply _
  have h := gram_eigenvalue_eq (familySynthesis v)
  rw [familySynthesis_gram, ← he] at h
  rw [← h (matrixSpectralData M (familyGram_positive v)) D]
  exact matrix_logDeterminant M (familyGram_positive v) hs

/--
Exact identity `logDeterminant D.eigenvalue s = log (Matrix.det ((1 : Matrix ι ι ℝ)+(s/2) •
Matrix.of (fun i j => inner ℝ (v i) (v j))))`.

Use: `chebyshev2.Continuum.finite_rankOne_logDeterminant` rewrites with this identity to
establish exact identity `logDeterminant D.eigenvalue s = (∑ i, log (1+s/2*e i))+ log
(1+s/2*u*(‖v‖^2-∑ i, (s/2)*e i/(1+s/2*e i)*(inner ℝ (b i) v)^2))`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Use the identities/estimates `chebyshev2.Continuum.familyGram_logDeterminant` with
the arguments shown in the proof.
-/
theorem familyGram_logDeterminant_of_eq {T : FeatureSpace →L[ℝ] FeatureSpace}
    (D : PositiveSpectralData T) (v : ι → FeatureSpace)
    (h : (∑ i, InnerProductSpace.rankOne ℝ (v i) (v i))=T)
    {s : ℝ} (hs : 0 ≤ s) :
    logDeterminant D.eigenvalue s =
      log (Matrix.det ((1 : Matrix ι ι ℝ)+(s/2) •
        Matrix.of (fun i j => inner ℝ (v i) (v j)))) := by
  -- Use the identities/estimates `chebyshev2.Continuum.familyGram_logDeterminant` with the
  -- arguments shown in the proof.
  subst T
  exact familyGram_logDeterminant v D hs

end
end chebyshev2.Continuum
