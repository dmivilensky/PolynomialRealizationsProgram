import krylov.Methods.BroydenModel

set_option autoImplicit false
/-!
Article: main_krylov, def:classes, genuine Broyden endpoint and secant identities.
Use: identify the actual convex-family BFGS endpoint with the existing real two-loop executor and verify the genuine secant equation of every true interpolation.
Source: proved actual inverse endpoint maps and their genuine physical actions, with real nonzero secant and inverse-curvature pivots.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual unit-parameter Broyden model has exactly the genuine existing inverse-BFGS two-loop action.
Use: The actual unit-parameter Broyden model has exactly the genuine existing inverse-BFGS two-loop action.
Article: main_krylov, def:classes, genuine Broyden endpoint and secant identities.
Proof: Induct through real observed pairs; its true interpolation selects the actual BFGS endpoint action. -/
theorem inverseBroydenModel_bfgs (c : ℝ) (W : List (E × E)) (v : E) :
    inverseBroydenModel c (fun _ => 1) W v=inverseBFGSApply c W v := by
  induction W generalizing v with
  | nil => rfl
  | cons p W ih =>
    simp only [inverseBroydenModel,inverseBroydenUpdate,sub_self,zero_smul,one_smul,zero_add,
      inverseBFGSUpdate_apply,ih,inverseBFGSApply]

/-- Every actual inverse Broyden interpolation satisfies the genuine secant equation on its true nonzero endpoint domains.
Use: Every actual inverse Broyden interpolation satisfies the genuine secant equation on its true nonzero endpoint domains.
Article: main_krylov, def:classes, genuine Broyden endpoint and secant identities.
Proof: Both actual endpoint models send the genuine secant image to its true step, and the real interpolation coefficients sum to one. -/
theorem inverseBroydenUpdate_secant (H : E →ₗ[ℝ] E) (s y : E) (θ : ℝ)
    (hsy : inner ℝ s y≠0) (hy : inner ℝ y (H y)≠0) :
    inverseBroydenUpdate H s y θ y=s := by
  -- Both genuine endpoint updates solve the actual same secant equation before interpolation.
  have hdfp : inverseDFPUpdate H s y y=s := by
    rw [inverseDFPUpdate_apply,div_self hy,div_self hsy,one_smul,one_smul,sub_self,zero_add]
  have hbfgs : inverseBFGSUpdate H s y y=s := by
    rw [inverseBFGSUpdate_apply]
    simp only [inv_mul_cancel₀ hsy,one_smul,sub_self,map_zero,inner_zero_right,mul_zero,sub_zero,zero_add]
  rw [inverseBroydenUpdate,LinearMap.add_apply,LinearMap.smul_apply,LinearMap.smul_apply,hdfp,hbfgs]
  module

/-- The genuine Broyden policy at its actual BFGS endpoint is exactly the existing full-memory two-loop BFGS implementation.
Use: The genuine Broyden policy at its actual BFGS endpoint is exactly the existing full-memory two-loop BFGS implementation.
Article: main_krylov, def:classes, genuine Broyden endpoint and secant identities.
Proof: Use the actual full-window identity and proved genuine endpoint model action. -/
theorem broydenMethod_bfgs (c : ℝ) :
    (broydenMethod c (fun _ => 1) : ProbedMethod E)=lbfgsMethod fullMemory (fun _ => c) := by
  unfold broydenMethod lbfgsMethod
  congr 1
  funext H
  change -inverseBroydenModel c (fun _ => 1) H.pairs H.gradient=
    -inverseBFGSApply c (selectedWindow fullMemory H) H.gradient
  rw [selectedWindow_full,inverseBroydenModel_bfgs]
end
end krylov.Methods
