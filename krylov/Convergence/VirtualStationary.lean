import krylov.Convergence.VirtualLocalization

/-!
Article: main_krylov, thm:V and restarted rows of Table s7-orders.
Use: include true stationary restart tails without a nonzero-direction or
inverse-domain assumption. Actual zero projected model right-hand sides
give zero virtual corrections and zero queried steps in the literal policy.
Source: the genuine one-gradient executor and linear model solves.
-/
namespace krylov.Convergence
noncomputable section
open krylov.Methods krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A true zero gradient has zero virtual model correction, regardless of
window rank or the totalized inverse branch. Article: thm:V. -/
theorem virtualCorrection_zero (W : List (E × E)) : virtualCorrection W 0=0 := by
  rw [virtualCorrection,virtualCoefficients,
    modelCoefficients_zero _ _ _ (by ext i; simp only [coordinates,inner_zero_right,Pi.zero_apply])]
  simp only [combine,Pi.zero_apply,zero_smul,Finset.sum_const_zero]

/-- The true virtual gradient at a zero current gradient is zero.
Article: thm:V, stationary execution. -/
theorem virtualGradient_zero (W : List (E × E)) : virtualGradient W 0=0 := by
  rw [virtualGradient,virtualCoefficients,
    modelCoefficients_zero _ _ _ (by ext i; simp only [coordinates,inner_zero_right,Pi.zero_apply])]
  simp only [combine,Pi.zero_apply,zero_smul,Finset.sum_const_zero,zero_add]

/-- Actual XRFC requests and outputs vanish on every zero-gradient
history, independently of the trial value. Article: thm:V. -/
theorem xrfc_policy_stationary (trial : History E → ℝ) (H : History E) (hg : H.gradient=0) :
    (xrfcMethod fullMemory trial).step H=0 ∧(xrfcMethod fullMemory trial).output H=0 := by
  simp only [xrfcMethod,hg,virtualCorrection_zero,virtualGradient_zero,windowDirection_zero,
    smul_zero,add_zero,and_self]

omit [InnerProductSpace ℝ E] in
/-- A one-gradient policy that fixes zero observed gradients preserves
the actual stationary query transcript exactly. Article: thm:V. -/
theorem oneGradientFunctionRun_stationary
    (m : OneGradientMethod E) (G : E → E) (x₀ : E) (hG : G x₀=0)
    (hstep : ∀ H : History E,H.gradient=0 → m.step H=0) (N : ℕ) :
    (oneGradientFunctionRun m G x₀ N).gradient=0 ∧
      (oneGradientFunctionRun m G x₀ N).displacement=0 := by
  induction N with
  | zero=>exact ⟨hG,rfl⟩
  | succ i ih=>
    have hs := hstep (oneGradientFunctionRun m G x₀ i) ih.1
    constructor
    · change G (x₀+(oneGradientFunctionRun m G x₀ i).displacement+
        m.step (oneGradientFunctionRun m G x₀ i))=0
      rw [ih.2,hs,add_zero,add_zero,hG]
    · change m.step (oneGradientFunctionRun m G x₀ i)+(oneGradientFunctionRun m G x₀ i).displacement=0
      rw [hs,ih.2,add_zero]

/-- The true unevaluated XRFC output fixes a stationary initial point.
Article: thm:V, including all zero-error restart tails. -/
theorem xrfcFunctionOutput_stationary {n : ℕ}
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) (hG : G x₀=0) : xrfcFunctionOutput trial G x₀=x₀ := by
  have hs := oneGradientFunctionRun_stationary (xrfcMethod fullMemory trial) G x₀ hG
    (fun H hH=>(xrfc_policy_stationary trial H hH).1) n
  have ho := (xrfc_policy_stationary trial _ hs.1).2
  rw [xrfcFunctionOutput,oneGradientFunctionOutput,oneGradientFunctionPoint,hs.2,ho,add_zero,add_zero]

end
end krylov.Convergence
