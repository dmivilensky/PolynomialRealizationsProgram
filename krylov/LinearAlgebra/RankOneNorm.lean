import krylov.Secant.MSS
import chebyshev1.Spectral.OperatorNorm
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
Article: main_krylov, thm:window, apA:galerkin and apG:mss.
Use: exact norms of actual physical rank-one matrices in the Euclidean operator norm.
Source: mathlib's exact norm of a Hilbert rank-one continuous linear map.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix
open scoped Matrix InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- A real rank-one matrix is the same actual Hilbert-space rank-one operator.
Use: transfer the already proved exact Hilbert rank-one norm to spectral matrices.
Article: main_krylov, thm:window and apG:mss, hhᵀ.
Proof: both operators send v to the same real pairing times their left vector. -/
theorem toEuclideanCLM_rankOne (u v : Fin n → ℝ) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (vecMulVec u v) =
      InnerProductSpace.rankOne ℝ (WithLp.toLp 2 u) (WithLp.toLp 2 v) := by
  ext w i
  simp only [Matrix.ofLp_toEuclideanCLM, krylov.Secant.outer_mulVec,
    InnerProductSpace.rankOne_apply, EuclideanSpace.inner_eq_star_dotProduct,
    star_trivial, PiLp.smul_apply, Pi.smul_apply, smul_eq_mul, dotProduct_comm]

/-- The spectral norm of a real outer product is exactly the product of its Euclidean norms.
Use: the hidden information witnesses and oldest-dual amplification constants are sharp.
Article: main_krylov, thm:window and apG:mss, exact rank-one norm.
Source: mathlib InnerProductSpace.norm_rankOne.
Proof: identify the actual matrix with its rank-one Hilbert operator and reuse its norm. -/
theorem spectral_norm_rankOne (u v : Fin n → ℝ) :
    chebyshev1.opNorm (vecMulVec u v) = ‖WithLp.toLp 2 u‖ * ‖WithLp.toLp 2 v‖ := by
  rw [chebyshev1.opNorm, Matrix.cstar_norm_def, toEuclideanCLM_rankOne,
    InnerProductSpace.norm_rankOne]

/-- Congruence of a normalized rank-one form uses the actual transformed generating vector.
Use: canonical normalization of the two hidden oldest-coordinate witnesses.
Article: main_krylov, thm:window, the printed canonical rank-one errors.
Proof: the rank-one compression identity also applies to the inverse coordinate matrix. -/
theorem rankOne_inverse_congruence (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.IsSymm)
    (v : Fin n → ℝ) :
    Q * vecMulVec v v * Q = vecMulVec (Q *ᵥ v) (Q *ᵥ v) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  have hv : v ᵥ* Q = Q *ᵥ v := by
    conv_lhs => rw [← hQ.eq]
    rw [vecMul_transpose]
  rw [hv]

end
end krylov.LinearAlgebra
