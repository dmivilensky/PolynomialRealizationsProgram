import polyak.CertifiedExamples.Plateaus.SourceRoot
import polyak.Certificates.PartII.Plateaus.PrimaryNumerical

/-! Actual coefficient, matrix and adjugate-kernel enclosures, and the exact
rank/kernel equalities derived from the genuine scalar boundary root. -/
noncomputable section
namespace polyak.CertifiedExamples.Plateaus
open General Levels Matrix LeanCert.Core chebyshev2.Numerics
open polyak.Certificates.PartII.Plateaus
open scoped BigOperators

theorem tuning18_Xi_mem : ∀i,coefficientVector tuning18 i∈row18Xi i :=
  row18_Xi_mem tuning18 rfl rfl tuning18_kappa_mem

theorem tuning21_Xi_mem : ∀i,coefficientVector tuning21 i∈row21Xi i :=
  row21_Xi_mem tuning21 rfl rfl tuning21_kappa_mem

theorem coordinates18_mem : ∀i,coordinates18 i∈row18Cosines i := by
  rw [coordinates18_eq]
  exact row18_cosines_mem

theorem coordinates21_mem : ∀i,coordinates21 i∈row21Cosines i := by
  rw [coordinates21_eq]
  exact row21_cosines_mem

def point18 : Fin 5→ℝ := ![coefficientVector tuning18 0,coefficientVector tuning18 1,
  coefficientVector tuning18 2,coordinates18 0,coordinates18 1]
def point21 : Fin 6→ℝ := ![coefficientVector tuning21 0,coefficientVector tuning21 1,
  coefficientVector tuning21 2,coordinates21 0,coordinates21 1,coordinates21 2]

theorem point18_mem : ∀i,point18 i∈row18CoordinateBox i := by
  intro i
  fin_cases i
  · exact tuning18_Xi_mem 0
  · exact tuning18_Xi_mem 1
  · exact tuning18_Xi_mem 2
  · exact coordinates18_mem 0
  · exact coordinates18_mem 1

theorem point21_mem : ∀i,point21 i∈row21CoordinateBox i := by
  intro i
  fin_cases i
  · exact tuning21_Xi_mem 0
  · exact tuning21_Xi_mem 1
  · exact tuning21_Xi_mem 2
  · exact coordinates21_mem 0
  · exact coordinates21_mem 1
  · exact coordinates21_mem 2

theorem row18LagExpr_actual (n:ℤ) (i:Fin 2) :
    (row18LagExpr n 0 i).value point18=
      Farey.Certificates.signedLagPolynomial tuning18 n (coordinates18 i) := by
  unfold row18LagExpr
  rw [coordinateCodeExpr_value]
  fin_cases i <;>
    change coordinateCodeValue (coefficientVector tuning18) n 0 _=_ <;>
      rw [coordinateCodeValue_zero,coordinateLag_actual_coefficients] <;> rfl

theorem row21LagExpr_actual (n:ℤ) (i:Fin 3) :
    (row21LagExpr n 0 i).value point21=
      Farey.Certificates.signedLagPolynomial tuning21 n (coordinates21 i) := by
  unfold row21LagExpr
  rw [coordinateCodeExpr_value]
  fin_cases i <;>
    change coordinateCodeValue (coefficientVector tuning21) n 0 _=_ <;>
      rw [coordinateCodeValue_zero,coordinateLag_actual_coefficients] <;> rfl

theorem sourceMatrix18_mem (r i:Fin 2) : sourceMatrix18 r i∈row18Matrix r i := by
  have h:=enclosed_sound _ _ _ (row18_matrix_checked r i) point18 point18_mem
  rw [row18LagExpr_actual,←sourceMatrix18_actual] at h
  exact h

theorem sourceMatrix21_mem (r i:Fin 3) : sourceMatrix21 r i∈row21Matrix r i := by
  have h:=enclosed_sound _ _ _ (row21_matrix_checked r i) point21 point21_mem
  rw [row21LagExpr_actual,←sourceMatrix21_actual] at h
  exact h

theorem matrixPoint18_mem : ∀i,matrixPoint sourceMatrix18 i∈row18MatrixBox i :=
  fun _i=>sourceMatrix18_mem _ _

theorem matrixPoint21_mem : ∀i,matrixPoint sourceMatrix21 i∈row21MatrixBox i :=
  fun _i=>sourceMatrix21_mem _ _

theorem rho18_mem (i:Fin 2) : rho18 i∈row18Right i := by
  have h:=enclosed_sound _ _ _ (row18_right_checked i) (matrixPoint sourceMatrix18) matrixPoint18_mem
  change (right2Expr (matrixVariables 2) i).value (matrixPoint sourceMatrix18)∈_ at h
  rw [right2Expr_value,matrixVariables_values] at h
  exact h

theorem mu18_mem (i:Fin 2) : mu18 i∈row18Left i := by
  have h:=enclosed_sound _ _ _ (row18_left_checked i) (matrixPoint sourceMatrix18) matrixPoint18_mem
  change (left2Expr (matrixVariables 2) i).value (matrixPoint sourceMatrix18)∈_ at h
  rw [left2Expr_value,matrixVariables_values] at h
  exact h

theorem rho21_mem (i:Fin 3) : rho21 i∈row21Right i := by
  have h:=enclosed_sound _ _ _ (row21_right_checked i) (matrixPoint sourceMatrix21) matrixPoint21_mem
  change (right3Expr (matrixVariables 3) i).value (matrixPoint sourceMatrix21)∈_ at h
  rw [right3Expr_value,matrixVariables_values] at h
  exact h

theorem mu21_mem (i:Fin 3) : mu21 i∈row21Left i := by
  have h:=enclosed_sound _ _ _ (row21_left_checked i) (matrixPoint sourceMatrix21) matrixPoint21_mem
  change (left3Expr (matrixVariables 3) i).value (matrixPoint sourceMatrix21)∈_ at h
  rw [left3Expr_value,matrixVariables_values] at h
  exact h

theorem rho18_positive (i:Fin 2) : 0<rho18 i := by
  have hp:0<(row18Right i).lo:=row18_right_positive i
  have hpR:(0:ℝ)<(row18Right i).lo:=by exact_mod_cast hp
  exact hpR.trans_le (rho18_mem i).1

theorem rho21_positive (i:Fin 3) : 0<rho21 i := by
  have hp:0<(row21Right i).lo:=row21_right_positive i
  have hpR:(0:ℝ)<(row21Right i).lo:=by exact_mod_cast hp
  exact hpR.trans_le (rho21_mem i).1

end polyak.CertifiedExamples.Plateaus
