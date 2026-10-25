import polyak.CertifiedExamples.Plateaus.DualSource
import polyak.CertifiedExamples.Plateaus.SourceMatrix
import polyak.CertifiedExamples.Plateaus.Evaluation
import polyak.CertifiedExamples.Plateaus.Pinning

/-! Every dual weight is bounded by a rejecting check of its actual defining
matrix and Cramer solve. The exported intervals are not assumed premises. -/
noncomputable section
namespace polyak.CertifiedExamples.Plateaus
open General Levels Matrix LeanCert.Core chebyshev2.Numerics
open polyak.Certificates.PartII.Plateaus

theorem row18LagExpr_prime (n : ℤ) (i : Fin 2) :
    (row18LagExpr n 1 i).value point18=
      coordinateCodeValue (coefficientVector tuning18) n 1 (coordinates18 i) := by
  unfold row18LagExpr
  rw [coordinateCodeExpr_value]
  fin_cases i <;> rfl

theorem row21LagExpr_prime (n : ℤ) (i : Fin 3) :
    (row21LagExpr n 1 i).value point21=
      coordinateCodeValue (coefficientVector tuning21) n 1 (coordinates21 i) := by
  unfold row21LagExpr
  rw [coordinateCodeExpr_value]
  fin_cases i <;> rfl

theorem slope18_mem (i r : Fin 2) : slope18 i r∈row18Slope i r := by
  have h:=enclosed_sound _ _ _ (row18_slope_checked r i) point18 point18_mem
  rw [value_minus,row18LagExpr_prime,row18LagExpr_prime] at h
  exact h

theorem slope21_mem (i r : Fin 3) : slope21 i r∈row21Slope i r := by
  have h:=enclosed_sound _ _ _ (row21_slope_checked r i) point21 point21_mem
  rw [value_minus,row21LagExpr_prime,row21LagExpr_prime] at h
  exact h

private theorem nonzero_of_box {x : ℝ} {I : IntervalRat} (hx : x∈I)
    (hI : I.hi<0 ∨ 0<I.lo) : x≠0 := by
  rcases hI with hI | hI
  · have hi : (I.hi:ℝ)<0 := by exact_mod_cast hI
    exact (hx.2.trans_lt hi).ne
  · have hi : (0:ℝ)<I.lo := by exact_mod_cast hI
    exact (hi.trans_le hx.1).ne'

theorem slope18_det_mem : slope18.det∈row18SlopeDet := by
  have hv : ∀i,matrixPoint slope18 i∈row18SlopeBox i := fun i=>slope18_mem _ _
  have h:=enclosed_sound _ _ _ row18_slope_det_checked (matrixPoint slope18) hv
  change (det2Expr (matrixVariables 2)).value (matrixPoint slope18)∈_ at h
  rwa [det2Expr_value,matrixVariables_values] at h

theorem slope21_det_mem : slope21.det∈row21SlopeDet := by
  have hv : ∀i,matrixPoint slope21 i∈row21SlopeBox i := fun i=>slope21_mem _ _
  have h:=enclosed_sound _ _ _ row21_slope_det_checked (matrixPoint slope21) hv
  change (det3Expr (matrixVariables 3)).value (matrixPoint slope21)∈_ at h
  rwa [det3Expr_value,matrixVariables_values] at h

theorem slope18_det_ne : slope18.det≠0 :=
  nonzero_of_box slope18_det_mem (by kernel_decide)

theorem slope21_det_ne : slope21.det≠0 :=
  nonzero_of_box slope21_det_mem (by kernel_decide)

def targetPoint18 : Fin 7 → ℝ :=
  ![coefficientVector tuning18 0,coefficientVector tuning18 1,coefficientVector tuning18 2,
    coordinates18 0,coordinates18 1,mu18 0,mu18 1]
def targetPoint21 : Fin 9 → ℝ :=
  ![coefficientVector tuning21 0,coefficientVector tuning21 1,coefficientVector tuning21 2,
    coordinates21 0,coordinates21 1,coordinates21 2,mu21 0,mu21 1,mu21 2]

theorem targetPoint18_mem : ∀i,targetPoint18 i∈row18TargetBox i := by
  intro i
  fin_cases i
  · exact tuning18_Xi_mem 0
  · exact tuning18_Xi_mem 1
  · exact tuning18_Xi_mem 2
  · exact coordinates18_mem 0
  · exact coordinates18_mem 1
  · exact mu18_mem 0
  · exact mu18_mem 1

theorem targetPoint21_mem : ∀i,targetPoint21 i∈row21TargetBox i := by
  intro i
  fin_cases i
  · exact tuning21_Xi_mem 0
  · exact tuning21_Xi_mem 1
  · exact tuning21_Xi_mem 2
  · exact coordinates21_mem 0
  · exact coordinates21_mem 1
  · exact coordinates21_mem 2
  · exact mu21_mem 0
  · exact mu21_mem 1
  · exact mu21_mem 2

theorem target18_expression (i : Fin 2) :
    (row18TargetExpr i).value targetPoint18=target18 i := by
  fin_cases i <;>
    simp only [row18TargetExpr,value_neg,value_plus,value_times,coordinateCodeExpr_value,
      value_variable] <;>
    change -(mu18 0*coordinateCodeValue (coefficientVector tuning18) 1 1 _+
      mu18 1*coordinateCodeValue (coefficientVector tuning18) (-4) 1 _)=_ <;>
    simp only [target18,pairTarget,first18,Fin.sum_univ_two] <;> rfl

theorem target21_expression (i : Fin 3) :
    (row21TargetExpr i).value targetPoint21=target21 i := by
  fin_cases i <;>
    simp only [row21TargetExpr,value_neg,value_plus,value_times,coordinateCodeExpr_value,
      value_variable] <;>
    change -((mu21 0*coordinateCodeValue (coefficientVector tuning21) 1 1 _+
      mu21 1*coordinateCodeValue (coefficientVector tuning21) (-12) 1 _)+
      mu21 2*coordinateCodeValue (coefficientVector tuning21) (-4) 1 _)=_ <;>
    simp only [target21,pairTarget,first21,Fin.sum_univ_three,add_assoc] <;> rfl

theorem target18_mem (i : Fin 2) : target18 i∈row18Target i := by
  have h:=enclosed_sound _ _ _ (row18_target_checked i) targetPoint18 targetPoint18_mem
  rwa [target18_expression] at h

theorem target21_mem (i : Fin 3) : target21 i∈row21Target i := by
  have h:=enclosed_sound _ _ _ (row21_target_checked i) targetPoint21 targetPoint21_mem
  rwa [target21_expression] at h

theorem moments18_mem (i : Fin 2) : moments18 i∈row18Moments i := by
  have hv : ∀z,Fin.append (matrixPoint slope18) target18 z∈row18MomentBox z :=
    append_mem _ _ _ _ (fun z=>slope18_mem _ _) target18_mem
  have h:=enclosed_sound _ _ _ (row18_moments_checked i)
    (Fin.append (matrixPoint slope18) target18) hv
  change (moments2Expr (matrixBlock (a:=2)) (blockSecond (a:=4)) i).value
    (Fin.append (matrixPoint slope18) target18)∈_ at h
  rwa [moments2_block_value] at h

theorem moments21_mem (i : Fin 3) : moments21 i∈row21Moments i := by
  have hv : ∀z,Fin.append (matrixPoint slope21) target21 z∈row21MomentBox z :=
    append_mem _ _ _ _ (fun z=>slope21_mem _ _) target21_mem
  have h:=enclosed_sound _ _ _ (row21_moments_checked i)
    (Fin.append (matrixPoint slope21) target21) hv
  change (moments3Expr (matrixBlock (a:=3)) (blockSecond (a:=9)) i).value
    (Fin.append (matrixPoint slope21) target21)∈_ at h
  rwa [moments3_block_value] at h

def liftPoint18 : Fin 4 → ℝ := ![mu18 0,mu18 1,moments18 0,moments18 1]
def liftPoint21 : Fin 6 → ℝ := ![mu21 0,mu21 1,mu21 2,moments21 0,moments21 1,moments21 2]

theorem liftPoint18_mem : ∀i,liftPoint18 i∈row18LiftBox i := by
  intro i
  fin_cases i
  · exact mu18_mem 0
  · exact mu18_mem 1
  · exact moments18_mem 0
  · exact moments18_mem 1

theorem liftPoint21_mem : ∀i,liftPoint21 i∈row21LiftBox i := by
  intro i
  fin_cases i
  · exact mu21_mem 0
  · exact mu21_mem 1
  · exact mu21_mem 2
  · exact moments21_mem 0
  · exact moments21_mem 1
  · exact moments21_mem 2

theorem weights18_mem (i : Fin 4) : weights18 i∈row18DualBoxes i := by
  fin_cases i
  · exact enclosed_sound _ _ _ row18_lift0_checked liftPoint18 liftPoint18_mem
  · exact enclosed_sound _ _ _ row18_lift1_checked liftPoint18 liftPoint18_mem
  · exact enclosed_sound _ _ _ row18_lift2_checked liftPoint18 liftPoint18_mem
  · exact enclosed_sound _ _ _ row18_lift3_checked liftPoint18 liftPoint18_mem

theorem weights21_mem (i : Fin 6) : weights21 i∈row21DualBoxes i := by
  fin_cases i
  · exact enclosed_sound _ _ _ row21_lift0_checked liftPoint21 liftPoint21_mem
  · exact enclosed_sound _ _ _ row21_lift1_checked liftPoint21 liftPoint21_mem
  · exact enclosed_sound _ _ _ row21_lift2_checked liftPoint21 liftPoint21_mem
  · exact enclosed_sound _ _ _ row21_lift3_checked liftPoint21 liftPoint21_mem
  · exact enclosed_sound _ _ _ row21_lift4_checked liftPoint21 liftPoint21_mem
  · exact enclosed_sound _ _ _ row21_lift5_checked liftPoint21 liftPoint21_mem

theorem weights18_positive (i : Fin 4) : 0<weights18 i := by
  have hp : ∀j,0<(row18DualBoxes j).lo := by kernel_decide
  have hh : (0:ℝ)<(row18DualBoxes i).lo := by exact_mod_cast hp i
  exact hh.trans_le (weights18_mem i).1

theorem weights21_positive (i : Fin 6) : 0<weights21 i := by
  have hp : ∀j,0<(row21DualBoxes j).lo := by kernel_decide
  have hh : (0:ℝ)<(row21DualBoxes i).lo := by exact_mod_cast hp i
  exact hh.trans_le (weights21_mem i).1

end polyak.CertifiedExamples.Plateaus
