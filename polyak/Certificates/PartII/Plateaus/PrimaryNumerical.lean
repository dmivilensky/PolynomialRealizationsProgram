import polyak.Certificates.PartII.Plateaus.Data
import polyak.CertifiedExamples.Plateaus.CoordinateCode
import polyak.CertifiedExamples.Plateaus.KernelExpressions
import polyak.CertifiedExamples.Plateaus.Enclosure
import polyak.CertifiedExamples.Plateaus.Blocks
import polyak.CertifiedExamples.Plateaus.PinningCode

/-! Finite rejecting checks for the actual polynomial matrix, adjugate
kernels, derivative system and positive lifted dual weights. -/
namespace polyak.Certificates.PartII.Plateaus
open polyak.CertifiedExamples.Plateaus LeanCert.Core chebyshev2.Numerics

def row18CoordinateBox : Fin 5 → IntervalRat := ![row18Xi 0,row18Xi 1,row18Xi 2,row18Cosines 0,row18Cosines 1]

def row18LagExpr (n:ℤ) (order:ℕ) (i:Fin 2) : E 5 :=
  coordinateCodeExpr ![.variable 0,.variable 1,.variable 2] n order
    (.variable (Fin.natAdd 3 i))

theorem row18_matrix_checked : ∀ r i,
    enclosed (row18LagExpr ((![1,-4]:Fin 2→ℤ) r) 0 i)
      row18CoordinateBox (row18Matrix r i)=true := by kernel_decide

theorem row18_slope_checked : ∀ r i,
    enclosed (minus (row18LagExpr ((![19,14]:Fin 2→ℤ) r) 1 i)
      (row18LagExpr ((![1,-4]:Fin 2→ℤ) r) 1 i))
      row18CoordinateBox (row18Slope i r)=true := by kernel_decide

theorem row18_pinning_checked : ∀ r i,
    enclosed (pinningExpr 18 ![.variable 0,.variable 1,.variable 2]
      ((![1,-4]:Fin 2→ℤ) r) (.variable (Fin.natAdd 3 i)))
      row18CoordinateBox (row18Pinning i r)=true := by kernel_decide

def row18MatrixBox : Fin 4 → IntervalRat := fun z =>
  row18Matrix ((finProdFinEquiv (m:=2) (n:=2)).symm z).1 ((finProdFinEquiv (m:=2) (n:=2)).symm z).2

def row18MatrixVariables : Fin 2 → Fin 2 → E 4 := fun i j =>
  matrixVariables 2 i j

theorem row18_left_checked : ∀ i,
    enclosed (left2Expr row18MatrixVariables i) row18MatrixBox (row18Left i)=true := by
  kernel_decide

theorem row18_right_checked : ∀ i,
    enclosed (right2Expr row18MatrixVariables i) row18MatrixBox (row18Right i)=true := by
  kernel_decide

def row18SlopeBox : Fin 4 → IntervalRat := fun z =>
  row18Slope ((finProdFinEquiv (m:=2) (n:=2)).symm z).1 ((finProdFinEquiv (m:=2) (n:=2)).symm z).2

theorem row18_slope_det_checked :
    enclosed (det2Expr row18MatrixVariables) row18SlopeBox row18SlopeDet=true := by
  kernel_decide

def row18PinningBox : Fin 4 → IntervalRat := fun z =>
  row18Pinning ((finProdFinEquiv (m:=2) (n:=2)).symm z).1 ((finProdFinEquiv (m:=2) (n:=2)).symm z).2

theorem row18_pinning_det_checked :
    enclosed (det2Expr row18MatrixVariables) row18PinningBox row18PinningDet=true := by
  kernel_decide

theorem row18_rank_minor_checked :
    enclosed (row18MatrixVariables 1 1) row18MatrixBox row18RankMinor=true := by kernel_decide

def row18TargetBox : Fin 7 → IntervalRat := ![row18Xi 0,row18Xi 1,row18Xi 2,row18Cosines 0,row18Cosines 1,row18Left 0,row18Left 1]

theorem row18_target0_checked :
    enclosed (.neg (plus (times (.variable 5) (coordinateCodeExpr (d:=7) ![.variable 0,.variable 1,.variable 2] (1) 1 (.variable 3))) (times (.variable 6) (coordinateCodeExpr (d:=7) ![.variable 0,.variable 1,.variable 2] (-4) 1 (.variable 3))))) row18TargetBox (row18Target 0)=true := by kernel_decide

theorem row18_target1_checked :
    enclosed (.neg (plus (times (.variable 5) (coordinateCodeExpr (d:=7) ![.variable 0,.variable 1,.variable 2] (1) 1 (.variable 4))) (times (.variable 6) (coordinateCodeExpr (d:=7) ![.variable 0,.variable 1,.variable 2] (-4) 1 (.variable 4))))) row18TargetBox (row18Target 1)=true := by kernel_decide

def row18TargetExpr (i:Fin 2) : E 7 :=
  .neg (plus (times (.variable 5) (coordinateCodeExpr ![.variable 0,.variable 1,.variable 2] (1) 1 (.variable ⟨3+i.val,by omega⟩))) (times (.variable 6) (coordinateCodeExpr ![.variable 0,.variable 1,.variable 2] (-4) 1 (.variable ⟨3+i.val,by omega⟩))))

theorem row18_target_checked : ∀ i,
    enclosed (row18TargetExpr i) row18TargetBox (row18Target i)=true := by kernel_decide

def row18MomentBox : Fin 6 → IntervalRat := Fin.append row18SlopeBox row18Target

def row18MomentMatrix : Fin 2 → Fin 2 → E 6 := fun i j =>
  matrixBlock (a:=2) i j

def row18MomentTarget : Fin 2 → E 6 := fun i =>
  blockSecond (a:=4) i

theorem row18_moments_checked : ∀ i,
    enclosed (moments2Expr row18MomentMatrix row18MomentTarget i)
      row18MomentBox (row18Moments i)=true := by kernel_decide

def row18LiftBox : Fin 4 → IntervalRat := ![row18Left 0,row18Left 1,row18Moments 0,row18Moments 1]

theorem row18_lift0_checked :
    enclosed (minus (.variable 0) (.variable 2)) row18LiftBox (row18DualBoxes 0)=true := by kernel_decide

theorem row18_lift1_checked :
    enclosed (IntervalExpr.variable 2) row18LiftBox (row18DualBoxes 1)=true := by kernel_decide

theorem row18_lift2_checked :
    enclosed (minus (.variable 1) (.variable 3)) row18LiftBox (row18DualBoxes 2)=true := by kernel_decide

theorem row18_lift3_checked :
    enclosed (IntervalExpr.variable 3) row18LiftBox (row18DualBoxes 3)=true := by kernel_decide

def row21CoordinateBox : Fin 6 → IntervalRat := ![row21Xi 0,row21Xi 1,row21Xi 2,row21Cosines 0,row21Cosines 1,row21Cosines 2]

def row21LagExpr (n:ℤ) (order:ℕ) (i:Fin 3) : E 6 :=
  coordinateCodeExpr ![.variable 0,.variable 1,.variable 2] n order
    (.variable (Fin.natAdd 3 i))

theorem row21_matrix_checked : ∀ r i,
    enclosed (row21LagExpr ((![1,-12,-4]:Fin 3→ℤ) r) 0 i)
      row21CoordinateBox (row21Matrix r i)=true := by kernel_decide

theorem row21_slope_checked : ∀ r i,
    enclosed (minus (row21LagExpr ((![-20,9,-25]:Fin 3→ℤ) r) 1 i)
      (row21LagExpr ((![1,-12,-4]:Fin 3→ℤ) r) 1 i))
      row21CoordinateBox (row21Slope i r)=true := by kernel_decide

theorem row21_pinning_checked : ∀ r i,
    enclosed (pinningExpr 21 ![.variable 0,.variable 1,.variable 2]
      ((![1,-12,-4]:Fin 3→ℤ) r) (.variable (Fin.natAdd 3 i)))
      row21CoordinateBox (row21Pinning i r)=true := by kernel_decide

def row21MatrixBox : Fin 9 → IntervalRat := fun z =>
  row21Matrix ((finProdFinEquiv (m:=3) (n:=3)).symm z).1 ((finProdFinEquiv (m:=3) (n:=3)).symm z).2

def row21MatrixVariables : Fin 3 → Fin 3 → E 9 := fun i j =>
  matrixVariables 3 i j

theorem row21_left_checked : ∀ i,
    enclosed (left3Expr row21MatrixVariables i) row21MatrixBox (row21Left i)=true := by
  kernel_decide

theorem row21_right_checked : ∀ i,
    enclosed (right3Expr row21MatrixVariables i) row21MatrixBox (row21Right i)=true := by
  kernel_decide

def row21SlopeBox : Fin 9 → IntervalRat := fun z =>
  row21Slope ((finProdFinEquiv (m:=3) (n:=3)).symm z).1 ((finProdFinEquiv (m:=3) (n:=3)).symm z).2

theorem row21_slope_det_checked :
    enclosed (det3Expr row21MatrixVariables) row21SlopeBox row21SlopeDet=true := by
  kernel_decide

def row21PinningBox : Fin 9 → IntervalRat := fun z =>
  row21Pinning ((finProdFinEquiv (m:=3) (n:=3)).symm z).1 ((finProdFinEquiv (m:=3) (n:=3)).symm z).2

theorem row21_pinning_det_checked :
    enclosed (det3Expr row21MatrixVariables) row21PinningBox row21PinningDet=true := by
  kernel_decide

theorem row21_rank_minor_checked :
    enclosed (det2Expr (fun i j=>row21MatrixVariables (Fin.succ i) (Fin.succ j))) row21MatrixBox row21RankMinor=true := by kernel_decide

def row21TargetBox : Fin 9 → IntervalRat := ![row21Xi 0,row21Xi 1,row21Xi 2,row21Cosines 0,row21Cosines 1,row21Cosines 2,row21Left 0,row21Left 1,row21Left 2]

theorem row21_target0_checked :
    enclosed (.neg (plus (plus (times (.variable 6) (coordinateCodeExpr (d:=9) ![.variable 0,.variable 1,.variable 2] (1) 1 (.variable 3))) (times (.variable 7) (coordinateCodeExpr (d:=9) ![.variable 0,.variable 1,.variable 2] (-12) 1 (.variable 3)))) (times (.variable 8) (coordinateCodeExpr (d:=9) ![.variable 0,.variable 1,.variable 2] (-4) 1 (.variable 3))))) row21TargetBox (row21Target 0)=true := by kernel_decide

theorem row21_target1_checked :
    enclosed (.neg (plus (plus (times (.variable 6) (coordinateCodeExpr (d:=9) ![.variable 0,.variable 1,.variable 2] (1) 1 (.variable 4))) (times (.variable 7) (coordinateCodeExpr (d:=9) ![.variable 0,.variable 1,.variable 2] (-12) 1 (.variable 4)))) (times (.variable 8) (coordinateCodeExpr (d:=9) ![.variable 0,.variable 1,.variable 2] (-4) 1 (.variable 4))))) row21TargetBox (row21Target 1)=true := by kernel_decide

theorem row21_target2_checked :
    enclosed (.neg (plus (plus (times (.variable 6) (coordinateCodeExpr (d:=9) ![.variable 0,.variable 1,.variable 2] (1) 1 (.variable 5))) (times (.variable 7) (coordinateCodeExpr (d:=9) ![.variable 0,.variable 1,.variable 2] (-12) 1 (.variable 5)))) (times (.variable 8) (coordinateCodeExpr (d:=9) ![.variable 0,.variable 1,.variable 2] (-4) 1 (.variable 5))))) row21TargetBox (row21Target 2)=true := by kernel_decide

def row21TargetExpr (i:Fin 3) : E 9 :=
  .neg (plus (plus (times (.variable 6) (coordinateCodeExpr ![.variable 0,.variable 1,.variable 2] (1) 1 (.variable ⟨3+i.val,by omega⟩))) (times (.variable 7) (coordinateCodeExpr ![.variable 0,.variable 1,.variable 2] (-12) 1 (.variable ⟨3+i.val,by omega⟩)))) (times (.variable 8) (coordinateCodeExpr ![.variable 0,.variable 1,.variable 2] (-4) 1 (.variable ⟨3+i.val,by omega⟩))))

theorem row21_target_checked : ∀ i,
    enclosed (row21TargetExpr i) row21TargetBox (row21Target i)=true := by kernel_decide

def row21MomentBox : Fin 12 → IntervalRat := Fin.append row21SlopeBox row21Target

def row21MomentMatrix : Fin 3 → Fin 3 → E 12 := fun i j =>
  matrixBlock (a:=3) i j

def row21MomentTarget : Fin 3 → E 12 := fun i =>
  blockSecond (a:=9) i

theorem row21_moments_checked : ∀ i,
    enclosed (moments3Expr row21MomentMatrix row21MomentTarget i)
      row21MomentBox (row21Moments i)=true := by kernel_decide

def row21LiftBox : Fin 6 → IntervalRat := ![row21Left 0,row21Left 1,row21Left 2,row21Moments 0,row21Moments 1,row21Moments 2]

theorem row21_lift0_checked :
    enclosed (minus (.variable 0) (.variable 3)) row21LiftBox (row21DualBoxes 0)=true := by kernel_decide

theorem row21_lift1_checked :
    enclosed (IntervalExpr.variable 3) row21LiftBox (row21DualBoxes 1)=true := by kernel_decide

theorem row21_lift2_checked :
    enclosed (minus (.variable 1) (.variable 4)) row21LiftBox (row21DualBoxes 2)=true := by kernel_decide

theorem row21_lift3_checked :
    enclosed (IntervalExpr.variable 4) row21LiftBox (row21DualBoxes 3)=true := by kernel_decide

theorem row21_lift4_checked :
    enclosed (minus (.variable 2) (.variable 5)) row21LiftBox (row21DualBoxes 4)=true := by kernel_decide

theorem row21_lift5_checked :
    enclosed (IntervalExpr.variable 5) row21LiftBox (row21DualBoxes 5)=true := by kernel_decide

end polyak.Certificates.PartII.Plateaus
