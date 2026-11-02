import krylov.LinearAlgebra.RankOneNorm

/-!
Article: main_krylov, lem:terminal-fibre and apA:galerkin(d), genuine invertible matrix actions.
Use: instantiate the proved two-scenario radius with the actual physical matrix inverse.
Source: the isometric matrix/operator identification and nonsingular matrix cancellation.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix
open scoped Matrix Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The continuous linear equivalence given by an actual invertible real matrix and its actual inverse.
Use: information-radius bounds concern the original matrix model and its true inverse action.
Article: main_krylov, apA:galerkin(d) and lem:terminal-fibre.
Proof: cancel both actual matrix/inverse pairs through the matrix/operator equivalence. -/
def matrixEquiv (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsUnit M.det) :
    EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) where
  toLinearEquiv :=
    { toLinearMap := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M).toLinearMap
      invFun := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M⁻¹
      left_inv := fun v => by
        change Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M⁻¹
          (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M v)=v
        rw [← mul_apply_eq_comp, ← map_mul, nonsing_inv_mul _ hM, map_one, one_apply_eq_self]
      right_inv := fun v => by
        change Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M
          (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M⁻¹ v)=v
        rw [← mul_apply_eq_comp, ← map_mul, mul_nonsing_inv _ hM, map_one, one_apply_eq_self] }
  continuous_toFun := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M).continuous
  continuous_invFun := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M⁻¹).continuous

end
end krylov.LinearAlgebra
