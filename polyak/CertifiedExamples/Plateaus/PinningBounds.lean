import polyak.CertifiedExamples.Plateaus.DualBounds
import polyak.CertifiedExamples.Plateaus.DualStatic

/-! The nonsingular finite pinning matrices are the actual polynomial
matrices at the scalar boundary roots, then the actual sine matrices. -/
noncomputable section
namespace polyak.CertifiedExamples.Plateaus
open General Levels Matrix LeanCert.Core chebyshev2.Numerics
open polyak.Certificates.PartII.Plateaus

def pinning18 : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of (fun i r=>
  polynomialPinning 18 (coefficientVector tuning18) (first18 r) (coordinates18 i))
def pinning21 : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of (fun i r=>
  polynomialPinning 21 (coefficientVector tuning21) (first21 r) (coordinates21 i))

theorem pinning18_mem (i r : Fin 2) : pinning18 i r∈row18Pinning i r := by
  have h:=enclosed_sound _ _ _ (row18_pinning_checked r i) point18 point18_mem
  rw [pinningExpr_value] at h
  fin_cases r <;> fin_cases i <;> exact h

theorem pinning21_mem (i r : Fin 3) : pinning21 i r∈row21Pinning i r := by
  have h:=enclosed_sound _ _ _ (row21_pinning_checked r i) point21 point21_mem
  rw [pinningExpr_value] at h
  fin_cases r <;> fin_cases i <;> exact h

theorem pinning18_det_mem : pinning18.det∈row18PinningDet := by
  have hv : ∀i,matrixPoint pinning18 i∈row18PinningBox i := fun i=>pinning18_mem _ _
  have h:=enclosed_sound _ _ _ row18_pinning_det_checked (matrixPoint pinning18) hv
  change (det2Expr (matrixVariables 2)).value (matrixPoint pinning18)∈_ at h
  rwa [det2Expr_value,matrixVariables_values] at h

theorem pinning21_det_mem : pinning21.det∈row21PinningDet := by
  have hv : ∀i,matrixPoint pinning21 i∈row21PinningBox i := fun i=>pinning21_mem _ _
  have h:=enclosed_sound _ _ _ row21_pinning_det_checked (matrixPoint pinning21) hv
  change (det3Expr (matrixVariables 3)).value (matrixPoint pinning21)∈_ at h
  rwa [det3Expr_value,matrixVariables_values] at h

private theorem nonzero_of_box {x : ℝ} {I : IntervalRat} (hx : x∈I)
    (hI : I.hi<0 ∨ 0<I.lo) : x≠0 := by
  rcases hI with hI | hI
  · have hi : (I.hi:ℝ)<0 := by exact_mod_cast hI
    exact (hx.2.trans_lt hi).ne
  · have hi : (0:ℝ)<I.lo := by exact_mod_cast hI
    exact (hi.trans_le hx.1).ne'

theorem pinning18_det_ne : pinning18.det≠0 :=
  nonzero_of_box pinning18_det_mem (by kernel_decide)

theorem pinning21_det_ne : pinning21.det≠0 :=
  nonzero_of_box pinning21_det_mem (by kernel_decide)

theorem row18_actual_pinning_det : Matrix.det (fun i r : Fin 2=>
    Real.sin ((reps18 r:ℝ)*(atoms18 i:ℝ)-tuningCurve tuning18 (atoms18 i)))≠0 := by
  apply pinning_det_of_polynomial tuning18 atoms18
    (gridAtom_interior 18 (by norm_num)) (gridAtom_grid 18 (by norm_num))
    first18 reps18 row18_first_nonzero row18_first_mod
  convert pinning18_det_ne using 1
  congr 1
  ext i r
  simp only [pinning18,Matrix.of_apply,polynomialPinning,coefficientVector_actual,coordinates18]

theorem row21_actual_pinning_det : Matrix.det (fun i r : Fin 3=>
    Real.sin ((reps21 r:ℝ)*(atoms21 i:ℝ)-tuningCurve tuning21 (atoms21 i)))≠0 := by
  apply pinning_det_of_polynomial tuning21 atoms21
    (gridAtom_interior 21 (by norm_num)) (gridAtom_grid 21 (by norm_num))
    first21 reps21 row21_first_nonzero row21_first_mod
  convert pinning21_det_ne using 1
  congr 1
  ext i r
  simp only [pinning21,Matrix.of_apply,polynomialPinning,coefficientVector_actual,coordinates21]

end polyak.CertifiedExamples.Plateaus
