import krylov.Strings.DiscreteOperator
import jacobi.Finite.MatrixEncoding
import jacobi.Finite.OrderedSpectrum
import jacobi.Finite.NormalizedPolynomials
import jacobi.Finite.AlternatingConjugation
import krylov.Reference.Christoffel

/-!
Article: `main_krylov`, `apC:lem:stieltjes(a)`, actual finite spectral data.
The genuine normalized path operator is alternatingly conjugated to a
positive-edge Jacobi matrix. Existing irreducible Jacobi simplicity and
endpoint weight positivity construct its full probability spectral data.
The eigenbasis is transported back to the physical string operator.
Source: the finite spectral theorem and the existing `jacobi.Finite` package.
-/

namespace krylov.Strings.DiscreteString
noncomputable section
open Matrix chebyshev1 chebyshev2 jacobi.Finite
open scoped BigOperators Matrix.Norms.L2Operator

variable {N : ℕ} (S : DiscreteString N)

/-- The true alternating physical-coordinate sign matrix. -/
def signMatrix (_S : DiscreteString N) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  diagonal fun i ↦ (-1 : ℝ) ^ i.val

theorem signMatrix_sq : S.signMatrix * S.signMatrix = 1 := by
  ext i j
  simp only [signMatrix, diagonal_mul_diagonal, diagonal_apply, Matrix.one_apply]
  split_ifs with h
  · rw [← pow_two, jacobi.Finite.alternating_sq]
  · rfl

theorem signMatrix_transpose : S.signMatrixᵀ = S.signMatrix := by simp [signMatrix]

/-- Positive-edge orientation of the same actual string operator. -/
def positiveOperator := S.signMatrix * S.operator * S.signMatrix

theorem positiveOperator_apply (i j : Fin (N + 1)) :
    S.positiveOperator i j = (-1 : ℝ) ^ i.val * S.operator i j * (-1 : ℝ) ^ j.val := by
  simp only [positiveOperator, signMatrix, diagonal_mul, mul_diagonal]

theorem positiveOperator_isHermitian : S.positiveOperator.IsHermitian := by
  have h := S.operator_posSemidef.mul_mul_conjTranspose_same S.signMatrix
  have hs : S.signMatrixᴴ = S.signMatrix := by simp [signMatrix]
  rw [hs] at h
  exact h.isHermitian

theorem positiveOperator_tridiagonal (i j : Fin (N + 1))
    (hij : i.val + 1 < j.val ∨ j.val + 1 < i.val) : S.positiveOperator i j = 0 := by
  rw [positiveOperator_apply, S.operator_tridiagonal i j hij, mul_zero, zero_mul]

theorem positiveOperator_adjacent (i j : Fin (N + 1)) (hij : i.val + 1 = j.val) :
    S.positiveOperator i j = -S.operator i j := by
  rw [positiveOperator_apply]
  calc
    _ = S.operator i j * ((-1 : ℝ) ^ i.val * (-1 : ℝ) ^ j.val) := by ring
    _ = _ := by rw [← hij, jacobi.Finite.alternating_adjacent]; ring

/-- A genuine positive-edge Jacobi encoding of the physical string. -/
def jacobi : Jacobi (N + 1) := fromMatrix S.positiveOperator

theorem jacobi_matrix : S.jacobi.matrix = S.positiveOperator :=
  fromMatrix_eq _ S.positiveOperator_isHermitian
    (fun i j hij ↦ by rw [S.positiveOperator_adjacent i j hij]; exact neg_nonneg.mpr (S.operator_adjacent_neg i j hij).le)
    S.positiveOperator_tridiagonal

theorem jacobi_irreducible : S.jacobi.Irreducible := by
  intro k hk hkN
  change 0 < if h : 0 < k ∧ k < N + 1 then
    (S.positiveOperator ⟨k - 1, by omega⟩ ⟨k, hkN⟩) ^ 2 else 0
  rw [dite_eq_left ⟨hk, hkN⟩]
  apply sq_pos_of_ne_zero
  rw [S.positiveOperator_adjacent _ _ (by change k - 1 + 1 = k; omega)]
  exact neg_ne_zero.mpr (S.operator_adjacent_neg _ _ (by change k - 1 + 1 = k; omega)).ne

/-- The actual complete positive-edge eigenbasis, before physical sign transport. -/
def positiveBasis : SpectralBasis S.jacobi.matrix :=
  SpectralBasis.ofHermitian _ S.jacobi.matrix_isHermitian

/-- A complete actual eigenbasis of the original normalized physical string
operator. The alternating conjugacy leaves its first coordinate unchanged. -/
def spectralBasis : SpectralBasis S.operator where
  Q := S.signMatrix * S.positiveBasis.Q
  eigenvalues := S.positiveBasis.eigenvalues
  transpose_mul := by
    rw [transpose_mul, S.signMatrix_transpose]
    calc
      _ = S.positiveBasis.Qᵀ * (S.signMatrix * S.signMatrix) * S.positiveBasis.Q := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [S.signMatrix_sq, Matrix.mul_one, S.positiveBasis.transpose_mul]
  mul_transpose := by
    rw [transpose_mul, S.signMatrix_transpose]
    calc
      _ = S.signMatrix * (S.positiveBasis.Q * S.positiveBasis.Qᵀ) * S.signMatrix := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [S.positiveBasis.mul_transpose, Matrix.mul_one, S.signMatrix_sq]
  diagonalize := by
    rw [transpose_mul, S.signMatrix_transpose]
    calc
      _ = S.positiveBasis.Qᵀ * (S.signMatrix * S.operator * S.signMatrix) * S.positiveBasis.Q := by
        simp only [Matrix.mul_assoc]
      _ = diagonal S.positiveBasis.eigenvalues := by
        rw [← positiveOperator, ← S.jacobi_matrix]
        exact S.positiveBasis.diagonalize

/-- Every actual physical spectral value is simple. -/
theorem spectralBasis_injective : Function.Injective S.spectralBasis.eigenvalues :=
  basis_values_injective S.jacobi S.jacobi_irreducible S.positiveBasis

/-- Every genuine spectral atom has strictly positive boundary weight. -/
theorem spectralBasis_weight_pos (k : Fin (N + 1)) : 0 < S.spectralBasis.weight 0 k := by
  have h := S.jacobi.data.spectral_endpoint_positive S.positiveBasis
    S.jacobi.coupling_nonneg S.jacobi_irreducible
    (basis_values_injective S.jacobi S.jacobi_irreducible S.positiveBasis) k
  change 0 < (S.signMatrix * S.positiveBasis.Q) 0 k ^ 2
  simpa only [signMatrix, diagonal_mul, Fin.val_zero, pow_zero, one_mul, SpectralBasis.weight] using h.1

/-- Actual full-support probability spectral data of the string's unit left
atom: exactly `N+1` distinct atoms, with all weights proved positive. -/
def spectralData : DiscreteMeasure (N + 1) where
  node := S.spectralBasis.eigenvalues
  distinct := S.spectralBasis_injective
  weight := S.spectralBasis.weight 0
  positive := S.spectralBasis_weight_pos
  probability := S.spectralBasis.weight_sum 0

end
end krylov.Strings.DiscreteString
