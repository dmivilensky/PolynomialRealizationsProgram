import polyak.CertifiedExamples.Plateaus.CoefficientBounds
import polyak.Certificates.PartII.Plateaus.Data

/-! Independent rejecting arithmetic checks for actual Xi coefficients and I4. -/
namespace polyak.Certificates.PartII.Plateaus
open polyak.CertifiedExamples.Plateaus chebyshev2.Numerics

theorem row18_coefficient0_checked :
    enclosed (coefficientExpr row18Y row18Beta 0) (coefficientBox row18Kappa) (row18Xi 0)=true :=
  by kernel_decide

theorem row18_coefficient1_checked :
    enclosed (coefficientExpr row18Y row18Beta 1) (coefficientBox row18Kappa) (row18Xi 1)=true :=
  by kernel_decide

theorem row18_coefficient2_checked :
    enclosed (coefficientExpr row18Y row18Beta 2) (coefficientBox row18Kappa) (row18Xi 2)=true :=
  by kernel_decide

theorem row18_coefficients_checked :
    ∀i,enclosed (coefficientExpr row18Y row18Beta i) (coefficientBox row18Kappa) (row18Xi i)=true := by
  intro i
  fin_cases i
  · exact row18_coefficient0_checked
  · exact row18_coefficient1_checked
  · exact row18_coefficient2_checked

theorem row18_gap0_checked :
    (IntervalExpr.neg (gapTestExpr 0)).strictNegative row18Xi=true := by kernel_decide

theorem row18_gap1_checked :
    (IntervalExpr.neg (gapTestExpr 1)).strictNegative row18Xi=true := by kernel_decide

theorem row18_gap2_checked :
    (IntervalExpr.neg (gapTestExpr 2)).strictNegative row18Xi=true := by kernel_decide

theorem row18_gap3_checked :
    (IntervalExpr.neg (gapTestExpr 3)).strictNegative row18Xi=true := by kernel_decide

theorem row18_gap4_checked :
    (IntervalExpr.neg (gapTestExpr 4)).strictNegative row18Xi=true := by kernel_decide

theorem row18_gap_checked :
    ∀i,(IntervalExpr.neg (gapTestExpr i)).strictNegative row18Xi=true := by
  intro i
  fin_cases i
  · exact row18_gap0_checked
  · exact row18_gap1_checked
  · exact row18_gap2_checked
  · exact row18_gap3_checked
  · exact row18_gap4_checked

theorem row21_coefficient0_checked :
    enclosed (coefficientExpr row21Y row21Beta 0) (coefficientBox row21Kappa) (row21Xi 0)=true :=
  by kernel_decide

theorem row21_coefficient1_checked :
    enclosed (coefficientExpr row21Y row21Beta 1) (coefficientBox row21Kappa) (row21Xi 1)=true :=
  by kernel_decide

theorem row21_coefficient2_checked :
    enclosed (coefficientExpr row21Y row21Beta 2) (coefficientBox row21Kappa) (row21Xi 2)=true :=
  by kernel_decide

theorem row21_coefficients_checked :
    ∀i,enclosed (coefficientExpr row21Y row21Beta i) (coefficientBox row21Kappa) (row21Xi i)=true := by
  intro i
  fin_cases i
  · exact row21_coefficient0_checked
  · exact row21_coefficient1_checked
  · exact row21_coefficient2_checked

theorem row21_gap0_checked :
    (IntervalExpr.neg (gapTestExpr 0)).strictNegative row21Xi=true := by kernel_decide

theorem row21_gap1_checked :
    (IntervalExpr.neg (gapTestExpr 1)).strictNegative row21Xi=true := by kernel_decide

theorem row21_gap2_checked :
    (IntervalExpr.neg (gapTestExpr 2)).strictNegative row21Xi=true := by kernel_decide

theorem row21_gap3_checked :
    (IntervalExpr.neg (gapTestExpr 3)).strictNegative row21Xi=true := by kernel_decide

theorem row21_gap4_checked :
    (IntervalExpr.neg (gapTestExpr 4)).strictNegative row21Xi=true := by kernel_decide

theorem row21_gap_checked :
    ∀i,(IntervalExpr.neg (gapTestExpr i)).strictNegative row21Xi=true := by
  intro i
  fin_cases i
  · exact row21_gap0_checked
  · exact row21_gap1_checked
  · exact row21_gap2_checked
  · exact row21_gap3_checked
  · exact row21_gap4_checked

end polyak.Certificates.PartII.Plateaus
