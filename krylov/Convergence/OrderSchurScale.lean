import krylov.Completion.SchurTrialRegularity
import krylov.Methods.HomogeneousSolve

/-!
Article: main_krylov, thm:D and s8:dcsdef, genuine DC estimate homogeneity.
Use: prove degree-zero common-scale invariance of the literal rational
Schur arithmetic estimate, including totalized singular supplied data.
Source: true bilinear Gram scaling and totalized inverse covariance.
-/
namespace krylov.Convergence
noncomputable section
open Matrix krylov.Methods krylov.Completion
variable {n p : ℕ}

/-- Actual Schur directional curvature scales quadratically under one
common nonzero scale of observed steps, secants and direction.
Article: main_krylov, thm:D, data-based DC estimate. -/
theorem schur_curvature_common_scale
    (S : Matrix (Fin n) (Fin p) ℝ) (d : Fin n → ℝ)
    (T : Matrix (Fin p) (Fin p) ℝ) (mu upper c : ℝ) (hc : c≠0) :
    schurLowerCurvature (c • S) (c • d) ((c*c) • T) mu=(c*c)*schurLowerCurvature S d T mu ∧
    schurUpperCurvature (c • S) (c • d) ((c*c) • T) upper=(c*c)*schurUpperCurvature S d T upper := by
  have hG : (c • S)ᵀ*(c • S)=(c*c) • (Sᵀ*S) := by
    rw [transpose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  have hb : (c • S)ᵀ*ᵥ (c • d)=(c*c) • (Sᵀ*ᵥ d) := by
    rw [transpose_smul,smul_mulVec,mulVec_smul,smul_smul]
  have hMlo : (c*c) • T-mu • ((c • S)ᵀ*(c • S))=(c*c) • (T-mu • (Sᵀ*S)) := by
    rw [hG,smul_comm mu (c*c),←smul_sub]
  have hMhi : upper • ((c • S)ᵀ*(c • S))-(c*c) • T=(c*c) • (upper • (Sᵀ*S)-T) := by
    rw [hG,smul_comm upper (c*c),←smul_sub]
  have hdot : (c • d) ⬝ᵥ (c • d)=(c*c)*(d ⬝ᵥ d) := by
    rw [smul_dotProduct,dotProduct_smul]
    simp only [smul_eq_mul]
    ring
  have hquad (M : Matrix (Fin p) (Fin p) ℝ) :
      ((c • S)ᵀ*ᵥ (c • d)) ⬝ᵥ (((c*c) • M)⁻¹*ᵥ ((c • S)ᵀ*ᵥ (c • d)))=
        (c*c)*((Sᵀ*ᵥ d) ⬝ᵥ (M⁻¹*ᵥ (Sᵀ*ᵥ d))) := by
    rw [hb,matrix_inv_scalar,smul_mulVec,mulVec_smul,smul_smul,
      inv_mul_cancel₀ (mul_ne_zero hc hc),one_smul,smul_dotProduct]
    rfl
  constructor
  · rw [schurLowerCurvature,schur_cross_contraction,hMlo,hquad,hdot,schurLowerCurvature,schur_cross_contraction]
    ring
  · rw [schurUpperCurvature,schur_cross_contraction,hMhi,hquad,hdot,schurUpperCurvature,schur_cross_contraction]
    ring

/-- The actual arithmetic Schur interval estimate is invariant under
common nonzero scaling; its true denominator zero conventions are retained.
Article: main_krylov, thm:D, original data-midpoint DC. -/
theorem schurArithmeticEstimate_common_scale
    (S : Matrix (Fin n) (Fin p) ℝ) (d : Fin n → ℝ)
    (T : Matrix (Fin p) (Fin p) ℝ) (mu upper q c : ℝ) (hc : c≠0) :
    schurArithmeticEstimate (c • S) (c • d) ((c*c) • T) mu upper ((c*c)*q)=
      schurArithmeticEstimate S d T mu upper q := by
  obtain ⟨hlo,hhi⟩:=schur_curvature_common_scale S d T mu upper c hc
  rw [schurArithmeticEstimate,hlo,hhi,schurArithmeticEstimate,_root_.mul_inv_rev,_root_.mul_inv_rev]
  calc
    _=((c*c)*(c*c)⁻¹)*(q*((schurLowerCurvature S d T mu)⁻¹+(schurUpperCurvature S d T upper)⁻¹)/2) := by ring
    _=_ := by rw [mul_inv_cancel₀ (mul_ne_zero hc hc),one_mul]

end
end krylov.Convergence
