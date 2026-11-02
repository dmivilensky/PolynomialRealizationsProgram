import krylov.Completion.FullActionRange
import krylov.Completion.ActionCurvatures
set_option autoImplicit false
/-!
Article: main_krylov, thm:radau, original full-action Schur curvature interval.
Use: assemble the proved actual full-action physical extrema and their true
singular Schur formulas into the attained original curvature interval.
Source: actual shorted-form endpoint constructions, genuine Loewner extrema
and explicit affine every-point attainment, including singular and collapsed cases.
-/

namespace krylov.Completion
noncomputable section
open Matrix krylov.LinearAlgebra
variable {n p : ℕ}

/-- Preserving the original entire observed action also preserves its true
compressed model and physical conjugacy constraint.
Use: full-action completions lie in the same original Gram-data completion class.
Article: main_krylov, thm:radau, full-action specialization.
Proof: transpose actual symmetric actions to preserve the real direction
pairing, and compress the original full-action identity on its true left columns. -/
theorem full_action_window_constraints
    (A C : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (hC : C.IsSymm)
    (S : Matrix (Fin n) (Fin p) ℝ) (d : Fin n → ℝ)
    (hact : C*S=A*S) (hzero : Sᵀ*ᵥ (A*ᵥ d)=0) :
    Sᵀ*C*S=Sᵀ*A*S ∧ Sᵀ*ᵥ (C*ᵥ d)=0 := by
  constructor
  · simpa only [Matrix.mul_assoc] using congrArg (fun M => Sᵀ*M) hact
  · have he := congrArg (fun M => Mᵀ*ᵥ d) hact
    simp only [transpose_mul,hA.eq,hC.eq,← Matrix.mulVec_mulVec] at he
    exact he.trans hzero

/-- The original full-action physical completion family has precisely the
printed singular-Schur curvature interval, and every point is genuinely attained.
Use: preserve the entire observed action AS while attaining both original
window endpoint curvatures, with no strict old spectral margin or ordinary inverse.
Article: main_krylov, thm:radau, full-action interval.
Proof: insert the actual lower and upper shorted-form quadratic formulas into
the proved genuine full-action curvature range. The latter already constructs
both physical endpoints and every intermediate real matrix on their affine segment. -/
theorem full_action_schur_curvature_range
    (A : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin p) ℝ) (d : Fin n → ℝ)
    (mu L c : ℝ) (hlo : (A-mu • 1).PosSemidef) (hhi : (L • 1-A).PosSemidef)
    (hzero : Sᵀ*ᵥ (A*ᵥ d)=0) :
    let hL := hlo.conjTranspose_mul_mul_same S
    let hH := hhi.conjTranspose_mul_mul_same S
    let b := Sᵀ*ᵥ d
    let cl := mu*(d ⬝ᵥ d)+mu^2*(b ⬝ᵥ (pseudoinverse (Sᵀ*(A-mu • 1)*S)
      (by simpa only [conjTranspose_eq_transpose_of_trivial] using hL.1)*ᵥ b))
    let ch := L*(d ⬝ᵥ d)-L^2*(b ⬝ᵥ (pseudoinverse (Sᵀ*(L • 1-A)*S)
      (by simpa only [conjTranspose_eq_transpose_of_trivial] using hH.1)*ᵥ b))
    (∃ C : Matrix (Fin n) (Fin n) ℝ,
      (C-mu • 1).PosSemidef ∧ (L • 1-C).PosSemidef ∧ C*S=A*S ∧ d ⬝ᵥ (C*ᵥ d)=c) ↔ c∈Set.Icc cl ch := by
  rw [full_action_curvature_range A S d mu L c hlo hhi,
    lower_action_curvature A S d mu hlo hzero,upper_action_curvature A S d L hhi hzero]
  rfl

end
end krylov.Completion
