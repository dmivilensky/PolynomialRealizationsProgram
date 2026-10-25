import polyak.Boundary.P5.CriticalJacobian
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
Article: Theorem p5h0, exact nonsingularity of both critical Jacobian blocks.
Use: these are submatrices of the actual Frechet Jacobian, rather than
independent invertibility data supplied to the implicit function theorem.
-/
noncomputable section
namespace polyak.Boundary.P5

/-- Article: the actual primal block in the source unknown order. -/
def primalMatrix : Matrix (Fin 4) (Fin 4) ℝ := !![criticalJacobian 0 0, criticalJacobian 0 1, criticalJacobian 0 4, criticalJacobian 0 3; criticalJacobian 1 0, criticalJacobian 1 1, criticalJacobian 1 4, criticalJacobian 1 3; criticalJacobian 2 0, criticalJacobian 2 1, criticalJacobian 2 4, criticalJacobian 2 3; criticalJacobian 3 0, criticalJacobian 3 1, criticalJacobian 3 4, criticalJacobian 3 3]

/-- Article: every entry of the block has its checked algebraic representation. -/
theorem primalMatrix_repr : primalMatrix=!![Polynomial.aeval y₀ primalEntry00, Polynomial.aeval y₀ primalEntry01, Polynomial.aeval y₀ primalEntry02, Polynomial.aeval y₀ primalEntry03; Polynomial.aeval y₀ primalEntry10, Polynomial.aeval y₀ primalEntry11, Polynomial.aeval y₀ primalEntry12, Polynomial.aeval y₀ primalEntry13; Polynomial.aeval y₀ primalEntry20, Polynomial.aeval y₀ primalEntry21, Polynomial.aeval y₀ primalEntry22, Polynomial.aeval y₀ primalEntry23; Polynomial.aeval y₀ primalEntry30, Polynomial.aeval y₀ primalEntry31, Polynomial.aeval y₀ primalEntry32, Polynomial.aeval y₀ primalEntry33] := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact primal_entry_0_0
  · exact primal_entry_0_1
  · exact primal_entry_0_2
  · exact primal_entry_0_3
  · exact primal_entry_1_0
  · exact primal_entry_1_1
  · exact primal_entry_1_2
  · exact primal_entry_1_3
  · exact primal_entry_2_0
  · exact primal_entry_2_1
  · exact primal_entry_2_2
  · exact primal_entry_2_3
  · exact primal_entry_3_0
  · exact primal_entry_3_1
  · exact primal_entry_3_2
  · exact primal_entry_3_3

/-- Article: the genuine primal block determinant equals the specified element of ℚ(y₀). -/
theorem primalMatrix_det : primalMatrix.det=primalDet₀ := by
  rw [primalMatrix_repr]
  rw [Matrix.det_succ_row_zero]
  norm_num [Matrix.det_fin_three,Fin.sum_univ_succ,Matrix.submatrix_apply,Fin.succAbove,
    primalEntry00,primalEntry01,primalEntry02,primalEntry03,primalEntry10,primalEntry11,primalEntry12,primalEntry13,primalEntry20,primalEntry21,primalEntry22,primalEntry23,primalEntry30,primalEntry31,primalEntry32,primalEntry33,primalDet₀,primalDetPolynomial]
  ring

/-- Article: no singularity in the actual primal critical Jacobian block. -/
theorem primalMatrix_det_ne_zero : primalMatrix.det ≠ 0 := by
  rw [primalMatrix_det]
  exact critical_block_determinants_ne_zero.2

/-- Article: the actual dual block in the source unknown order. -/
def dualMatrix : Matrix (Fin 3) (Fin 3) ℝ := !![criticalJacobian 4 2, criticalJacobian 4 5, criticalJacobian 4 6; criticalJacobian 5 2, criticalJacobian 5 5, criticalJacobian 5 6; criticalJacobian 6 2, criticalJacobian 6 5, criticalJacobian 6 6]

/-- Article: every entry of the block has its checked algebraic representation. -/
theorem dualMatrix_repr : dualMatrix=!![Polynomial.aeval y₀ dualEntry00, Polynomial.aeval y₀ dualEntry01, Polynomial.aeval y₀ dualEntry02; Polynomial.aeval y₀ dualEntry10, Polynomial.aeval y₀ dualEntry11, Polynomial.aeval y₀ dualEntry12; Polynomial.aeval y₀ dualEntry20, Polynomial.aeval y₀ dualEntry21, Polynomial.aeval y₀ dualEntry22] := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact dual_entry_0_0
  · exact dual_entry_0_1
  · exact dual_entry_0_2
  · exact dual_entry_1_0
  · exact dual_entry_1_1
  · exact dual_entry_1_2
  · exact dual_entry_2_0
  · exact dual_entry_2_1
  · exact dual_entry_2_2

/-- Article: the genuine dual block determinant equals the specified element of ℚ(y₀). -/
theorem dualMatrix_det : dualMatrix.det=dualDet₀ := by
  rw [dualMatrix_repr]
  norm_num [Matrix.det_fin_three,Fin.sum_univ_succ,Matrix.submatrix_apply,Fin.succAbove,
    dualEntry00,dualEntry01,dualEntry02,dualEntry10,dualEntry11,dualEntry12,dualEntry20,dualEntry21,dualEntry22,dualDet₀,dualDetPolynomial]
  linear_combination (-1713860167500*y₀^3/43243231 - 3567900365100*y₀^2/43243231 - 4482557254125*y₀/172972924 + 4615184389275/691891696) * y₀_equation

/-- Article: no singularity in the actual dual critical Jacobian block. -/
theorem dualMatrix_det_ne_zero : dualMatrix.det ≠ 0 := by
  rw [dualMatrix_det]
  exact critical_block_determinants_ne_zero.1

end polyak.Boundary.P5
