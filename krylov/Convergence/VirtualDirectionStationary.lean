import krylov.Convergence.VirtualStationary
import krylov.Convergence.VirtualDirectionLocalization

/-!
Article: main_krylov, thm:V, literal direction-basis stationary tails.
Use: every actual replayed direction window gives zero correction and
zero query at a true zero gradient, including singular histories.
Source: genuine zero right-hand sides in the original policy.
-/
namespace krylov.Convergence
noncomputable section
open krylov.Methods krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual XRFC requests and outputs vanish on every zero-gradient
history, independently of the trial value. Article: thm:V. -/
theorem xrfcD_policy_stationary (trial : History E → ℝ) (H : History E) (hg : H.gradient=0) :
    (xrfcDMethod fullMemory trial).step H=0 ∧(xrfcDMethod fullMemory trial).output H=0 := by
  simp only [xrfcDMethod,hg,virtualCorrection_zero,virtualGradient_zero,windowDirection_zero,
    smul_zero,add_zero,and_self]

/-- The true unevaluated XRFC output fixes a stationary initial point.
Article: thm:V, including all zero-error restart tails. -/
theorem xrfcDFunctionOutput_stationary {n : ℕ}
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) (hG : G x₀=0) : xrfcDFunctionOutput trial G x₀=x₀ := by
  have hs := oneGradientFunctionRun_stationary (xrfcDMethod fullMemory trial) G x₀ hG
    (fun H hH=>(xrfcD_policy_stationary trial H hH).1) n
  have ho := (xrfcD_policy_stationary trial _ hs.1).2
  rw [xrfcDFunctionOutput,oneGradientFunctionOutput,oneGradientFunctionPoint,hs.2,ho,add_zero,add_zero]

end
end krylov.Convergence
