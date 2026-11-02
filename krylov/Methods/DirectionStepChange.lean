import krylov.LinearAlgebra.ObservedStepChange
import krylov.Methods.DirectionImageError
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), exact actual native S/D observed basis change.
Use: the recorded step/image pairs on the actual direction-basis execution
are exact common transforms of its genuine replayed directions/images.
Source: actual native virtual coefficients, real evaluated queries and
the true observed inverse-trial replay definition, on arbitrary operators.
-/

namespace krylov.Methods
noncomputable section
open Matrix krylov.LinearAlgebra
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual recorded-step change matrix on a genuine native D history.
Use: its real entries are exactly the actual earlier virtual coefficients
and the actual selected native trials, before any asymptotic analysis.
Article: main_krylov, thm:local(a), true native observed step change. -/
def xrfcDObservedStepChange (trial : History E → ℝ) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    Matrix (Fin k) (Fin k) ℝ :=
  observedStepChange
    (fun j : Fin k => trial (oneGradientRun (xrfcDMethod fullMemory trial) A g (k-1-j.val)))
    (fun j : Fin k => xrfcDArrayCoefficients trial A g (k-1-j.val))

/-- Every actually recorded native D evaluated step is exactly the
genuine observed change applied to the real replay direction family.
Use: this dictionary compares S and D fields on the same actual history,
without assuming their off-quadratic virtual gradients coincide.
Article: main_krylov, thm:local(a), exact genuine native step synthesis.
Proof: the real evaluated step is its actual old virtual correction plus
the selected trial times the true new direction. The generic exact finite
column synthesis and true native age dictionary give those same terms. -/
theorem xrfcDObservedStepChange_steps (trial : History E → ℝ)
    (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) (j : Fin k) :
    combine (fun i : Fin k => xrfcDExecutedDirection trial A g (k-1-i.val))
      (fun i => xrfcDObservedStepChange trial A g k i j)=
        oneGradientStep (xrfcDMethod fullMemory trial) A g (k-1-j.val) := by
  rw [xrfcDObservedStepChange,observedStepChange_column]
  simp only [oldColumnIndex_age]
  have hc : virtualCorrection (xrfcDWindow trial A g (k-1-j.val))
      (oneGradientRun (xrfcDMethod fullMemory trial) A g (k-1-j.val)).gradient=
      combine (fun r => xrfcDExecutedDirection trial A g (k-1-j.val-1-r.val))
        (xrfcDArrayCoefficients trial A g (k-1-j.val)) :=
    (xrfcD_virtual_coordinates trial A g (k-1-j.val)).1
  rw [← hc]
  rfl

/-- Every actual step image recorded by the native D execution is the
same genuine observed change applied to its real data-only replay images.
The unknown operators enter only the already returned true query images.
Use: recorded S and native D pair arrays have one exact common change;
no varying-operator replay-image correctness is assumed.
Article: main_krylov, thm:local(a), exact genuine native image synthesis.
Proof: the real replay image is the actual new gradient minus its actual
virtual gradient divided by the selected nonzero trial. Its true virtual
gradient is the incoming observation plus the real old replay combination.
The actual returned-gradient recursion cancels that same incoming gradient. -/
theorem xrfcDObservedStepChange_images (trial : History E → ℝ)
    (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) (j : Fin k)
    (ht : trial (oneGradientRun (xrfcDMethod fullMemory trial) A g (k-1-j.val))≠0) :
    combine (fun i : Fin k => xrfcDExecutedImage trial A g (k-1-i.val))
      (fun i => xrfcDObservedStepChange trial A g k i j)=
        A (k-1-j.val) (oneGradientStep (xrfcDMethod fullMemory trial) A g (k-1-j.val)) := by
  rw [xrfcDObservedStepChange,observedStepChange_column]
  simp only [oldColumnIndex_age]
  let age := k-1-j.val
  let m := xrfcDMethod fullMemory trial
  have hq : trial (oneGradientRun m A g age) • xrfcDExecutedImage trial A g age=
      oneGradientGradient m A g (age+1)-xrfcDVirtualGradient trial A g age := by
    change trial (oneGradientRun m A g age) •
      ((trial (oneGradientRun m A g age))⁻¹ • (_-_))=_
    rw [smul_smul,mul_inv_cancel₀ ht,one_smul]
  change combine (fun r => xrfcDExecutedImage trial A g (age-1-r.val))
      (xrfcDArrayCoefficients trial A g age)+
      trial (oneGradientRun m A g age) • xrfcDExecutedImage trial A g age=
        A age (oneGradientStep m A g age)
  have hgv : xrfcDVirtualGradient trial A g age=oneGradientGradient m A g age+
      combine (fun r => xrfcDExecutedImage trial A g (age-1-r.val))
        (xrfcDArrayCoefficients trial A g age) := (xrfcD_virtual_coordinates trial A g age).2
  rw [hq,oneGradientGradient_succ,hgv]
  abel

end
end krylov.Methods
