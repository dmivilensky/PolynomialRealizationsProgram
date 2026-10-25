import polyak.CertifiedExamples.Plateaus.Source

/-! The genuine numerator boundary root forces the actual source matrix to be
singular, and hence gives exact adjugate kernel equalities. -/
noncomputable section
namespace polyak.CertifiedExamples.Plateaus
open General Levels Matrix
open scoped BigOperators

private theorem coordinate_matrix_det_zero {d:ℕ} (q:Tuning) (n:Fin d→ℤ) (c:Fin d→ℝ)
    (h:(sourceMatrix q.y q.beta q.kappa n c).det=0) :
    (coordinateMatrix (coefficientVector q) n c).det=0 := by
  have hm : sourceMatrix q.y q.beta q.kappa n c=
      xiDenominator q.y q.beta q.kappa • coordinateMatrix (coefficientVector q) n c := by
    ext r i
    change numeratorLag q.y q.beta q.kappa (n r) (c i)=
      xiDenominator q.y q.beta q.kappa*coordinateLag (coefficientVector q) (n r) (c i)
    rw [coordinateLag_actual_coefficients]
    exact numeratorLag_actual q (n r) (c i)
  rw [hm,Matrix.det_smul,Fintype.card_fin] at h
  have hd:xiDenominator q.y q.beta q.kappa≠0 := by
    unfold xiDenominator
    positivity [q.y_pos,q.kappa_gt_one,q.beta_lt_one]
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hd)

theorem sourceMatrix18_det_zero : sourceMatrix18.det=0 := by
  apply coordinate_matrix_det_zero
  rw [coordinates18_eq]
  exact tuning18_root

theorem sourceMatrix21_det_zero : sourceMatrix21.det=0 := by
  apply coordinate_matrix_det_zero
  rw [coordinates21_eq]
  exact tuning21_root

theorem rho18_kernel (r:Fin 2) :
    (∑i,rho18 i*Farey.Certificates.signedLagPolynomial tuning18 ((![1,-4]:Fin 2→ℤ) r)
      (coordinates18 i))=0 := by
  have h:=congrFun (positivePrimal_kernel sourceMatrix18 0 sourceMatrix18_det_zero) r
  simpa only [rho18,Matrix.mulVec,dotProduct,Pi.zero_apply,←sourceMatrix18_actual,mul_comm] using h

theorem rho21_kernel (r:Fin 3) :
    (∑i,rho21 i*Farey.Certificates.signedLagPolynomial tuning21 ((![1,-12,-4]:Fin 3→ℤ) r)
      (coordinates21 i))=0 := by
  have h:=congrFun (positivePrimal_kernel sourceMatrix21 0 sourceMatrix21_det_zero) r
  simpa only [rho21,Matrix.mulVec,dotProduct,Pi.zero_apply,←sourceMatrix21_actual,mul_comm] using h

end polyak.CertifiedExamples.Plateaus
