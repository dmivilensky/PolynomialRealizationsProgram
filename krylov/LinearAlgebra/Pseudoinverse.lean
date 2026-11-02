import chebyshev1.Spectral.Basis
import Mathlib.Analysis.Matrix.Order

/-!
Article: main_krylov, apA:galerkin(f), singular Schur completion.
Use: provide an actual Moore--Penrose inverse at singular endpoints, rather
than using the nonsingular inverse (which is zero for every singular matrix).
Source: spectral definition of the Moore--Penrose inverse; reuse the earlier
article's actual orthogonal spectral-basis construction and coordinate calculus.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix chebyshev1
open scoped Matrix MatrixOrder
variable {n : ℕ}

/-- Spectral inversion of the nonzero eigenvalues, with zero eigenvalues kept zero.
Use: the concrete singular inverse in generalized Schur complements.
Article: main_krylov, apA:galerkin(f), the operator A⁺.
Source: the Moore--Penrose inverse of a real symmetric matrix. -/
def pseudoinverseInBasis {A : Matrix (Fin n) (Fin n) ℝ} (B : SpectralBasis A) :
    Matrix (Fin n) (Fin n) ℝ :=
  B.Q * diagonal (fun i => (B.eigenvalues i)⁻¹) * B.Qᵀ

/-- The canonical Moore--Penrose inverse obtained from the genuine finite spectral theorem.
Use: all singular completion statements refer to this actual matrix.
Article: main_krylov, apA:galerkin(f), A⁺. -/
def pseudoinverse (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    Matrix (Fin n) (Fin n) ℝ := pseudoinverseInBasis (SpectralBasis.ofHermitian A hA)

/-- The actual pseudoinverse diagonalizes to reciprocal eigenvalues, including zeros.
Use: verify the Penrose equations and singular range identities by scalar algebra.
Article: main_krylov, apA:galerkin(f).
Proof: cancel the orthogonal change of basis on both sides of the diagonal. -/
theorem coordinates_pseudoinverse {A : Matrix (Fin n) (Fin n) ℝ} (B : SpectralBasis A) :
    B.coordinates (pseudoinverseInBasis B) = diagonal (fun i => (B.eigenvalues i)⁻¹) := by
  unfold SpectralBasis.coordinates pseudoinverseInBasis
  simp only [← Matrix.mul_assoc, B.transpose_mul, one_mul]
  rw [Matrix.mul_assoc, B.transpose_mul, mul_one]

/-- The constructed singular inverse is a genuinely symmetric matrix.
Use: the Schur correction remains a symmetric form at singular endpoints.
Article: main_krylov, apA:galerkin(f).
Proof: transposition fixes the real diagonal and interchanges its orthogonal factors. -/
theorem pseudoinverse_isSymm {A : Matrix (Fin n) (Fin n) ℝ} (B : SpectralBasis A) :
    (pseudoinverseInBasis B).IsSymm := by
  simp only [pseudoinverseInBasis, Matrix.IsSymm, transpose_mul, transpose_transpose,
    diagonal_transpose, Matrix.mul_assoc]

/-- The first Penrose equation holds even when the original matrix is singular.
Use: reconstruct any vector in the original range through its pseudoinverse.
Article: main_krylov, apA:galerkin(f), AA⁺A=A.
Proof: in the reused actual spectral coordinates the identity is t*t⁻¹*t=t. -/
theorem pseudoinverse_penrose_left {A : Matrix (Fin n) (Fin n) ℝ} (B : SpectralBasis A) :
    A * pseudoinverseInBasis B * A = A := by
  apply B.coordinates_injective
  have hd : B.coordinates A = diagonal B.eigenvalues := B.diagonalize
  simp only [B.coordinates_mul, coordinates_pseudoinverse, hd, diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases h : B.eigenvalues i = 0 <;> simp [h]

/-- The second Penrose equation fixes the inverse on its supported spectral subspace.
Use: identify the actual inverse range and establish the singular Schur formula.
Article: main_krylov, apA:galerkin(f), A⁺AA⁺=A⁺.
Proof: invert each nonzero eigenvalue and use the total inverse at zero. -/
theorem pseudoinverse_penrose_right {A : Matrix (Fin n) (Fin n) ℝ} (B : SpectralBasis A) :
    pseudoinverseInBasis B * A * pseudoinverseInBasis B = pseudoinverseInBasis B := by
  apply B.coordinates_injective
  have hd : B.coordinates A = diagonal B.eigenvalues := B.diagonalize
  simp only [B.coordinates_mul, coordinates_pseudoinverse, hd, diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases h : B.eigenvalues i = 0 <;> simp [h]

/-- The original matrix commutes with its spectral pseudoinverse.
Use: both range projectors satisfy the remaining symmetric Penrose equations.
Article: main_krylov, apA:galerkin(f), symmetry of AA⁺ and A⁺A.
Proof: their diagonal coordinate products commute pointwise. -/
theorem pseudoinverse_commute {A : Matrix (Fin n) (Fin n) ℝ} (B : SpectralBasis A) :
    A * pseudoinverseInBasis B = pseudoinverseInBasis B * A := by
  apply B.coordinates_injective
  have hd : B.coordinates A = diagonal B.eigenvalues := B.diagonalize
  simp only [B.coordinates_mul, coordinates_pseudoinverse, hd, diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

/-- The Moore--Penrose lift exactly reconstructs every vector in the true matrix range.
Use: turn the singular Schur range condition into a concrete solved cross block.
Article: main_krylov, apA:galerkin(f), range compatibility at a singular endpoint.
Proof: represent the vector as Az and apply AA⁺A=A. -/
theorem pseudoinverse_on_range {A : Matrix (Fin n) (Fin n) ℝ} (B : SpectralBasis A)
    {x : Fin n → ℝ} (hx : x ∈ LinearMap.range A.mulVecLin) :
    A *ᵥ (pseudoinverseInBasis B *ᵥ x) = x := by
  obtain ⟨z, rfl⟩ := hx
  change A *ᵥ (pseudoinverseInBasis B *ᵥ (A *ᵥ z)) = A *ᵥ z
  rw [mulVec_mulVec, mulVec_mulVec, pseudoinverse_penrose_left B]

/-- A rectangular cross block has compatible range exactly when its pseudoinverse lift solves it.
Use: express the article's range conditions with an explicit matrix equation.
Article: main_krylov, apA:galerkin(f), ran X ⊆ ran A.
Proof: lift each range vector by the constructed inverse; conversely the solved
matrix equation itself supplies a preimage for every cross-block action. -/
theorem pseudoinverse_range_iff {p : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (B : SpectralBasis A) (X : Matrix (Fin n) (Fin p) ℝ) :
    LinearMap.range X.mulVecLin ≤ LinearMap.range A.mulVecLin ↔
      A * pseudoinverseInBasis B * X = X := by
  -- Lift actual cross-block actions; zero eigenvalues never require cancellation.
  constructor
  · intro hr
    have he (v : Fin p → ℝ) : (A * pseudoinverseInBasis B * X) *ᵥ v = X *ᵥ v := by
      rw [← mulVec_mulVec, ← mulVec_mulVec]
      exact pseudoinverse_on_range B (hr ⟨v, rfl⟩)
    ext i j
    have h := congrFun (he (Pi.single j 1)) i
    simpa only [Matrix.mulVec_single, op_smul_eq_smul, one_smul, Matrix.col,
      Matrix.transpose_apply] using h
  · intro he x hx
    obtain ⟨v, rfl⟩ := hx
    refine ⟨pseudoinverseInBasis B *ᵥ (X *ᵥ v), ?_⟩
    change A *ᵥ (pseudoinverseInBasis B *ᵥ (X *ᵥ v)) = X *ᵥ v
    rw [mulVec_mulVec, mulVec_mulVec, he]

/-- The spectral range projector is symmetric, including at zero eigenvalues.
Use: transfer kernel annihilation on one side into the Schur range condition.
Article: main_krylov, apA:galerkin(f), symmetric Moore--Penrose range projector.
Proof: transpose the two symmetric factors and use their proved commutation. -/
theorem pseudoinverse_projector_isSymm {A : Matrix (Fin n) (Fin n) ℝ}
    (B : SpectralBasis A) (hA : A.IsSymm) : (A * pseudoinverseInBasis B).IsSymm := by
  rw [Matrix.IsSymm, transpose_mul, (pseudoinverse_isSymm B).eq, hA.eq,
    ← pseudoinverse_commute B]

/-- The complement of the actual spectral range projector lies in the kernel.
Use: the necessary singular range condition follows by testing these null directions.
Article: main_krylov, apA:galerkin(f), the kernel-range decomposition.
Proof: commute A with A⁺ and apply the first Penrose identity. -/
theorem pseudoinverse_kernel_projector {A : Matrix (Fin n) (Fin n) ℝ}
    (B : SpectralBasis A) : A * (1 - A * pseudoinverseInBasis B) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, pseudoinverse_commute B,
    ← Matrix.mul_assoc, pseudoinverse_penrose_left B, sub_self]

/-- The actual Moore--Penrose inverse agrees with the ordinary inverse on invertible forms.
Use: strict spectral gaps reduce the full singular block criterion to the scalar interval formula.
Article: main_krylov, apA:galerkin(f), strict hidden-entry completion.
Proof: left-multiply the proved Penrose equation to obtain a genuine left inverse,
then use uniqueness of the nonsingular inverse. -/
theorem pseudoinverse_eq_inv (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hunit : IsUnit A.det) : pseudoinverse A hA = A⁻¹ := by
  have h := congrArg (fun X => A⁻¹ * X)
    (pseudoinverse_penrose_left (chebyshev1.SpectralBasis.ofHermitian A hA))
  simp only [← Matrix.mul_assoc, nonsing_inv_mul A hunit, Matrix.one_mul] at h
  exact (Matrix.inv_eq_left_inv h).symm

end
end krylov.LinearAlgebra
