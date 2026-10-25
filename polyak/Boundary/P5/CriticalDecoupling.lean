import polyak.Boundary.P5.CriticalSystem

/-!
Article: Theorem p5h0, exact decoupling and the dual consistency determinant.
Use: the reduced three-by-three system eliminates the two dual weights and
produces the actual quintic equation, before selecting its isolated root.
-/
noncomputable section
namespace polyak.Boundary.P5
open Polynomial

/-- Article: the reduced critical dual equation 0, linear in the two weights. -/
def dualReduced0 (y w2 w3 : ℝ) : ℝ := 96*w2*y^5 - 48*w2*y^4 - 168*w2*y^3 + 30*w2*y^2 + 81*w2*y + 24*w2 + 96*w3*y^5 - 48*w3*y^4 - 208*w3*y^3 + 80*w3*y^2 + 116*w3*y - 26*w3 - 96*y^5 + 48*y^4 + 168*y^3 - 60*y^2 - 96*y + 6

/-- Article: the reduced critical dual equation 1, linear in the two weights. -/
def dualReduced1 (_y w2 w3 : ℝ) : ℝ := -3*w2 + 22*w3 - 12

/-- Article: the reduced critical dual equation 2, linear in the two weights. -/
def dualReduced2 (y w2 w3 : ℝ) : ℝ := 1152*w2*y^5 - 1536*w2*y^3 - 324*w2*y^2 + 384*w2*y + 129*w2 + 1152*w3*y^5 - 1856*w3*y^3 - 144*w3*y^2 + 624*w3*y + 64*w3 - 1152*y^5 + 1536*y^3 + 144*y^2 - 504*y - 84

/-- Article: exact interpretation of reduced critical dual equation 0. -/
theorem critical_dual_reduced_0 (Z : Coordinates) :
    regularSystem (0,Z) 4=-(2*Z 2+1)*dualReduced0 (Z 2) (Z 5) (Z 6)/4 := by
  rw [regularSystem_zero_4]
  norm_num [C4,C4Part0,C4Part1,polynomialValue,dualReduced0]
  ring

/-- Article: exact interpretation of reduced critical dual equation 1. -/
theorem critical_dual_reduced_1 (Z : Coordinates) :
    regularSystem (0,Z) 5=dualReduced1 (Z 2) (Z 5) (Z 6) := by
  rw [regularSystem_zero_5]
  norm_num [C5,C5Part0,polynomialValue,dualReduced1]
  ring

/-- Article: exact interpretation of reduced critical dual equation 2. -/
theorem critical_dual_reduced_2 (Z : Coordinates) :
    regularSystem (0,Z) 6=-dualReduced2 (Z 2) (Z 5) (Z 6)/4 := by
  rw [regularSystem_zero_6]
  norm_num [C6,C6Part0,C6Part1,polynomialValue,dualReduced2]
  ring

/-- Article: the three linear equations' consistency matrix in (w₂,w₃,1). -/
def dualConsistency (y : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![96*y^5 - 48*y^4 - 168*y^3 + 30*y^2 + 81*y + 24,96*y^5 - 48*y^4 - 208*y^3 + 80*y^2 + 116*y - 26,-96*y^5 + 48*y^4 + 168*y^3 - 60*y^2 - 96*y + 6;
     -3,22,-12;
     1152*y^5 - 1536*y^3 - 324*y^2 + 384*y + 129,1152*y^5 - 1856*y^3 - 144*y^2 + 624*y + 64,-1152*y^5 + 1536*y^3 + 144*y^2 - 504*y - 84]

/-- Article: the exact source consistency determinant is 900(2y+1)³q₅(y). -/
theorem dualConsistency_det (y : ℝ) :
    (dualConsistency y).det=900*(2*y+1)^3*(32*y^5-40*y^4+16*y^3-6*y^2-12*y+3) := by
  norm_num [dualConsistency,Matrix.det_fin_three]
  ring

end polyak.Boundary.P5
