import krylov.OneGradient.NativeLastLaunch
import krylov.OneGradient.LastLaunchTrialRemainder
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), actual native measured relative trial error.
Use: name the true post-query relative line error of the implemented S/D
program, without feeding the unknown current operator into its policy.
Source: actual native observed virtual fields and exact real line algebra.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Methods krylov.Reference
variable {n : ℕ}

/-- The actual native S/D relative trial error at the genuine current
queried direction and virtual gradient. The current unknown operator is
used only to measure the error after the real query, never by the policy.
Use: canonical incoming and cubic output formulas retain the actual trial
error instead of replacing it by a formal derivative or limiting scalar.
Article: main_krylov, thm:local(a), genuine native epsilon. -/
def xrfcNativeTrialError (directions : Bool) (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) : ℝ :=
  let m := xrfcBasisMethod directions trial
  let H := oneGradientRun m A g k
  let s := xrfcNativeColumns directions trial A g k
  let y := xrfcNativeImages directions trial A g k
  let w := modelCoefficients s (pairModel s y) H.gradient
  let gv := H.gradient+combine y w
  let d := conjugacyDirection s y gv
  lastLaunchTrialError (trial H) d gv (A k)

/-- The actual measured error quantity is exactly one minus the true
trial divided by its real measured exact-search length, with Lean's total
zero conventions included. No positivity premise is needed for this identity.
Use: the actual native epsilon in the row formulas is the source relative
line error, rather than an independent curvature-error definition.
Article: main_krylov, thm:local(a), exact measured trial-error dictionary.
Proof: substitute the actual real exact-search quotient and use the true
field division-of-a-quotient identity, then cancel the two real minus signs. -/
theorem lastLaunchTrialError_eq_relative
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (tau : ℝ) (d gv : E) (A : E →L[ℝ] E) :
    lastLaunchTrialError tau d gv A=1-tau/lineLength gv d (A d) := by
  rw [lastLaunchTrialError,lineLength,div_div_eq_mul_div,div_neg,sub_neg_eq_add]

end
end krylov.OneGradient
