import krylov.XR.RobustStationary

/-!
Article: main_krylov, thm:metric, literal positive regularized solve.
Use: prove the actual N-squared-plus-lambda inverse domain and its
commutation with N before solving the genuine robust normal equations.
Source: positivity of N transpose N and exact ordinary matrix inversion.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {p : ℕ}

/-- The literal Tikhonov matrix of the reduced robust problem.
Article: main_krylov, thm:metric. -/
def robustRegularizedMatrix (N : Matrix (Fin p) (Fin p) ℝ) (lambda : ℝ) :
    Matrix (Fin p) (Fin p) ℝ := N*N+lambda • 1

/-- Every positive regularizer has a genuinely positive matrix, not a
totalized off-domain inverse. Article: thm:metric. -/
theorem robustRegularizedMatrix_posDef (N : Matrix (Fin p) (Fin p) ℝ)
    (hN : N.IsHermitian) (lambda : ℝ) (hl : 0<lambda) :
    (robustRegularizedMatrix N lambda).PosDef := by
  have hNN : (N*N).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial,hN.isSymm.eq] using
      Matrix.posSemidef_conjTranspose_mul_self N
  simpa only [robustRegularizedMatrix,add_comm] using
    (Matrix.PosDef.one.smul hl).add_posSemidef hNN

/-- The physical regularized action is the original squared-model
normal operator plus lambda times the true correction.
Article: main_krylov, thm:metric. -/
theorem robustRegularizedMatrix_action (N : Matrix (Fin p) (Fin p) ℝ)
    (lambda : ℝ) (b : EuclideanSpace ℝ (Fin p)) :
    cgOperator (robustRegularizedMatrix N lambda) b=cgOperator N (cgOperator N b)+lambda • b := by
  simp only [robustRegularizedMatrix,cgOperator,map_add,map_mul,map_smul,map_one,
    _root_.add_apply,_root_.smul_apply,mul_apply_eq_comp,one_apply_eq_self]

/-- The original model commutes with the actual positive regularized
inverse. Article: main_krylov, thm:metric. -/
theorem robustRegularizedMatrix_inv_commute (N : Matrix (Fin p) (Fin p) ℝ)
    (hN : N.IsHermitian) (lambda : ℝ) (hl : 0<lambda) :
    N*(robustRegularizedMatrix N lambda)⁻¹=(robustRegularizedMatrix N lambda)⁻¹*N := by
  let A := robustRegularizedMatrix N lambda
  have hA := robustRegularizedMatrix_posDef N hN lambda hl
  have hd := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  have hcomm : N*A=A*N := by
    simp only [A,robustRegularizedMatrix,Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,
      Matrix.smul_mul,Matrix.mul_one,Matrix.one_mul,Matrix.mul_assoc]
  calc
    _=(A⁻¹*A)*(N*A⁻¹) := by rw [nonsing_inv_mul _ hd,Matrix.one_mul]
    _=A⁻¹*((A*N)*A⁻¹) := by simp only [Matrix.mul_assoc]
    _=A⁻¹*((N*A)*A⁻¹) := by rw [hcomm]
    _=A⁻¹*N := by rw [Matrix.mul_assoc N A A⁻¹,mul_nonsing_inv _ hd,Matrix.mul_one]

/-- The true interior normal equation gives exactly the printed
Tikhonov correction formula with its actual ordinary inverse.
Article: main_krylov, thm:metric. -/
theorem robust_regularized_solve (N : Matrix (Fin p) (Fin p) ℝ) (hN : N.IsHermitian)
    (rho b : EuclideanSpace ℝ (Fin p)) (lambda : ℝ) (hl : 0<lambda)
    (hbalance : cgOperator N (rho+cgOperator N b)+lambda • b=0) :
    b= -(cgOperator (robustRegularizedMatrix N lambda)⁻¹ (cgOperator N rho)) := by
  have hA := robustRegularizedMatrix_posDef N hN lambda hl
  have hnormal : cgOperator (robustRegularizedMatrix N lambda) b= -(cgOperator N rho) := by
    rw [map_add,add_assoc] at hbalance
    rw [robustRegularizedMatrix_action]
    exact eq_neg_of_add_eq_zero_right hbalance
  have hi := congrArg (cgOperator (robustRegularizedMatrix N lambda)⁻¹) hnormal
  rw [threshold_inverse_cancel _ hA,map_neg] at hi
  exact hi

end
end krylov.XR
