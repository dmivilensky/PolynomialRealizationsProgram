import krylov.LinearAlgebra.FrobeniusSupport
import krylov.LinearAlgebra.RankOneNorm
import krylov.LinearAlgebra.HilbertSchmidtCompression

/-!
Article: main_krylov, lem:aggregate, simultaneous sharpness constructions.
Use: actual finite symmetric rank-two matrices realize the printed planar
blocks in arbitrary orthonormal physical directions.
Source: the proved rank-one operator bridge, finite Bessel and genuine Frobenius pairing.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix chebyshev1
open scoped Matrix InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual symmetric matrix with block (a,b;b,c) on the physical plane spanned by e,h.
Use: both spectral and Frobenius sharpness families use this concrete rank-two matrix.
Article: main_krylov, lem:aggregate, the printed attaining increment blocks. -/
def planarMatrix (e h : EuclideanSpace ℝ (Fin n)) (a b c : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  a • vecMulVec (WithLp.ofLp e) (WithLp.ofLp e) +
    b • (vecMulVec (WithLp.ofLp e) (WithLp.ofLp h) + vecMulVec (WithLp.ofLp h) (WithLp.ofLp e)) +
    c • vecMulVec (WithLp.ofLp h) (WithLp.ofLp h)

/-- Every actual planar witness matrix is symmetric.
Use: all attaining constructions remain in the article's symmetric perturbation class.
Article: main_krylov, lem:aggregate.
Proof: transpose each actual outer term and interchange the cross pair. -/
theorem planarMatrix_isSymm (e h : EuclideanSpace ℝ (Fin n)) (a b c : ℝ) :
    (planarMatrix e h a b c).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [planarMatrix, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  ring

/-- The actual planar matrix action has exactly its two printed scalar coordinates.
Use: verify every old-flag cross action and compressed action in the sharpness family.
Article: main_krylov, lem:aggregate, planar witness action.
Proof: use the actual matrix/rank-one bridge and collect its two vector coefficients. -/
theorem planarMatrix_action (e h : EuclideanSpace ℝ (Fin n)) (a b c : ℝ)
    (w : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (planarMatrix e h a b c) w =
      (a * inner ℝ e w + b * inner ℝ h w) • e +
        (b * inner ℝ e w + c * inner ℝ h w) • h := by
  simp only [planarMatrix, map_add, map_smul, toEuclideanCLM_rankOne, _root_.add_apply,
    _root_.smul_apply, InnerProductSpace.rankOne_apply]
  module

/-- Actual orthonormal planar coordinates have their exact Euclidean squared norm.
Use: compute the true spectral norm of the planar witness without an assumed block norm.
Article: main_krylov, lem:aggregate, spectral sharpness.
Proof: expand the squared norm and cancel the actual orthogonal cross pairing. -/
theorem planar_coordinates_norm_sq (e h : EuclideanSpace ℝ (Fin n))
    (he : ‖e‖ = 1) (hh : ‖h‖ = 1) (heh : inner ℝ e h = 0) (a b : ℝ) :
    ‖a • e + b • h‖^2 = a^2 + b^2 := by
  rw [norm_add_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, sq_abs, he, hh, mul_one,
    real_inner_smul_left, real_inner_smul_right, heh, mul_zero, add_zero]

/-- The actual planar spectral witness obeys the exact unit operator-norm budget.
Use: its scaled versions are admissible for every actual increment budget.
Article: main_krylov, lem:aggregate, spectral attaining family.
Proof: its squared output norm is the old two-coordinate energy; finite Bessel
controls that energy by the input norm, including directions outside the plane. -/
theorem planar_spectral_norm_le (e h : EuclideanSpace ℝ (Fin n)) (he : ‖e‖ = 1) (hh : ‖h‖ = 1)
    (heh : inner ℝ e h = 0) (s t : ℝ) (hst : s^2 + t^2 = 1) :
    opNorm (planarMatrix e h (-s) t s) ≤ 1 := by
  rw [opNorm, Matrix.cstar_norm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0 : ℝ) ≤ 1)
  intro w
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [planarMatrix_action, planar_coordinates_norm_sq e h he hh heh]
  -- The reflected two-plane block preserves exactly the input's two-coordinate energy.
  calc
    _ = (s^2 + t^2) * ((inner ℝ e w)^2 + (inner ℝ h w)^2) := by ring
    _ = (inner ℝ e w)^2 + (inner ℝ h w)^2 := by rw [hst, one_mul]
    _ ≤ _ := two_unit_bessel e h w he hh heh

/-- The actual planar matrix has precisely its three-coefficient Hilbert--Schmidt energy.
Use: verify the Frobenius sharpness family with its twice-counted symmetric cross block.
Article: main_krylov, lem:aggregate, ‖E‖_F²=a²+2b²+c².
Proof: expand the actual flattened inner product; orthonormal physical directions
annihilate every mixed outer-product pairing. -/
theorem planar_hsSq (e h : EuclideanSpace ℝ (Fin n)) (he : ‖e‖ = 1) (hh : ‖h‖ = 1)
    (heh : inner ℝ e h = 0) (a b c : ℝ) : hsSq (planarMatrix e h a b c) = a^2 + 2*b^2 + c^2 := by
  have hee : WithLp.ofLp e ⬝ᵥ WithLp.ofLp e = 1 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, he, one_pow] using
      real_inner_self_eq_norm_sq e
  have hhh : WithLp.ofLp h ⬝ᵥ WithLp.ofLp h = 1 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, hh, one_pow] using
      real_inner_self_eq_norm_sq h
  have hhe : WithLp.ofLp h ⬝ᵥ WithLp.ofLp e = 0 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using heh
  have heh' : WithLp.ofLp e ⬝ᵥ WithLp.ofLp h = 0 := by rw [dotProduct_comm, hhe]
  rw [← hsNorm_sq, ← norm_frobeniusVector, ← real_inner_self_eq_norm_sq]
  -- Compute the true flattened energy, keeping the Frobenius and spectral norms separate.
  simp only [planarMatrix, frobeniusVector_add, frobeniusVector_smul, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, frobenius_outer_pairing, hee, hhh, hhe, heh',
    mul_one, mul_zero, add_zero, zero_add]
  ring

end
end krylov.LinearAlgebra
