import krylov.Completion.ActionEndpoints
import krylov.LinearAlgebra.NormalizedRankOne
set_option autoImplicit false
/-!
Article: main_krylov, thm:radau, full-action endpoint curvatures.
Use: identify the actual constructed full-action extrema with the printed
singular Schur quadratic forms under the original conjugacy constraint.
Source: physical matrix pairings and the proved shorted positive action form.
-/

namespace krylov.Completion
noncomputable section
open Matrix krylov.LinearAlgebra
variable {n p : ℕ}

/-- The quadratic form of the actual shorted completion is the compressed
Moore--Penrose quadratic form of the actual observed action pairing.
Use: compute the extremal curvature without choosing an orthogonal complement basis.
Article: main_krylov, thm:radau.
Proof: move the observed action columns across the genuine Euclidean pairing. -/
theorem shorted_quadratic (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosSemidef)
    (S : Matrix (Fin n) (Fin p) ℝ) (d : Fin n → ℝ) :
    let hH := hM.conjTranspose_mul_mul_same S
    d ⬝ᵥ (shortedForm M hM S*ᵥ d)=
      ((M*S)ᵀ*ᵥ d) ⬝ᵥ (pseudoinverse (Sᵀ*M*S)
        (by simpa only [conjTranspose_eq_transpose_of_trivial] using hH.1)*ᵥ ((M*S)ᵀ*ᵥ d)) := by
  dsimp only
  dsimp only [shortedForm]
  rw [← mulVec_mulVec,← mulVec_mulVec,dotProduct_comm d,transpose_pairing,dotProduct_comm]

/-- The actual lower full-action endpoint has the exact singular Schur
curvature, even when its shifted old model is singular.
Use: attain the same lower endpoint with the entire constraint A'S=AS retained.
Article: main_krylov, thm:radau, full-action lower endpoint.
Proof: conjugacy removes the observed action term, leaving −μSᵀd in the
shorted quadratic formula, whose two scalar factors produce μ². -/
theorem lower_action_curvature (A : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin p) ℝ)
    (d : Fin n → ℝ) (mu : ℝ) (hlo : (A-mu • 1).PosSemidef)
    (hzero : Sᵀ*ᵥ (A*ᵥ d)=0) :
    let hH := hlo.conjTranspose_mul_mul_same S
    d ⬝ᵥ (lowerActionEndpoint A mu hlo S*ᵥ d)=
      mu*(d ⬝ᵥ d)+mu^2*((Sᵀ*ᵥ d) ⬝ᵥ (pseudoinverse (Sᵀ*(A-mu • 1)*S)
        (by simpa only [conjTranspose_eq_transpose_of_trivial] using hH.1)*ᵥ (Sᵀ*ᵥ d))) := by
  dsimp only
  have hcross : ((A-mu • 1)*S)ᵀ*ᵥ d= -mu • (Sᵀ*ᵥ d) := by
    rw [transpose_mul,hlo.1.isSymm.eq,← mulVec_mulVec,sub_mulVec,smul_mulVec,
      Matrix.one_mulVec,mulVec_sub,mulVec_smul,hzero,zero_sub,neg_smul]
  simp only [lowerActionEndpoint,add_mulVec,smul_mulVec,Matrix.one_mulVec,dotProduct_add,
    dotProduct_smul,smul_eq_mul]
  rw [shorted_quadratic,hcross]
  simp only [mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  ring

/-- The actual upper full-action endpoint has the exact singular Schur curvature.
Use: attain the same upper endpoint while preserving all measured action columns.
Article: main_krylov, thm:radau, full-action upper endpoint.
Proof: conjugacy leaves LSᵀd in the upper-shift action pairing; its quadratic
shorted correction is exactly L² times the actual compressed inverse form. -/
theorem upper_action_curvature (A : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin p) ℝ)
    (d : Fin n → ℝ) (L : ℝ) (hhi : (L • 1-A).PosSemidef)
    (hzero : Sᵀ*ᵥ (A*ᵥ d)=0) :
    let hH := hhi.conjTranspose_mul_mul_same S
    d ⬝ᵥ (upperActionEndpoint A L hhi S*ᵥ d)=
      L*(d ⬝ᵥ d)-L^2*((Sᵀ*ᵥ d) ⬝ᵥ (pseudoinverse (Sᵀ*(L • 1-A)*S)
        (by simpa only [conjTranspose_eq_transpose_of_trivial] using hH.1)*ᵥ (Sᵀ*ᵥ d))) := by
  dsimp only
  have hcross : ((L • 1-A)*S)ᵀ*ᵥ d=L • (Sᵀ*ᵥ d) := by
    rw [transpose_mul,hhi.1.isSymm.eq,← mulVec_mulVec,sub_mulVec,smul_mulVec,
      Matrix.one_mulVec,mulVec_sub,mulVec_smul,hzero,sub_zero]
  simp only [upperActionEndpoint,sub_mulVec,smul_mulVec,Matrix.one_mulVec,dotProduct_sub,
    dotProduct_smul,smul_eq_mul]
  rw [shorted_quadratic,hcross]
  simp only [mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  ring

end
end krylov.Completion
