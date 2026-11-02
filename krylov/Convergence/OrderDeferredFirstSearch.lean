import krylov.Convergence.OrderSearchOnlyInputs
import krylov.Functions.MetricFCOperators
import krylov.Cancellation.DCSlide

/-!
Article: main_krylov, thm:D and s7:N, literal first observed DC secant.
Use: DC's genuine first search and first Hessian average agree exactly
with FC before the final deferred branch, without source assumptions.
Source: direct execution of the empty observed window.
-/
namespace krylov.Convergence
noncomputable section
open krylov.Methods krylov.Functions krylov.Cancellation
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The original deferred policy shares FC's literal first scalar search.
Article: thm:D, actual s7:N reference dictionary. -/
theorem deferredFunctionPoint_one
    (memory : ℕ → ℕ) (N : ℕ) (hN : N≠1) (estimate : History E → ℝ)
    (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (r : ℝ) (x₀ : E) :
    scalarFunctionPoint (deferredDataMethod memory N estimate) T f G r x₀ 1=
      metricFCPoint T f G memory r x₀ 1 := by
  rw [show (1:ℕ)=0+1 by rfl,scalarSearchOnlyPoint_succ _ (fun _ _=>rfl)]
  simp only [scalarFunctionRun,scalarFunctionPoint,History.displacement,List.map_nil,List.sum_nil,add_zero]
  simp only [deferredDataMethod,show ¬([] : List (IterationRecord E)).length+1=N by simpa using hN.symm,
    ↓reduceIte,fcMethod,retainedMethod,selectedWindow,History.pairs,recordPairs,List.take_nil,History.gradient]
  simp only [metricFCPoint,exactSearchPoint,exactSearchHistory,metricFCDirection,List.map_cons,List.map_nil,
    ContinuousLinearEquiv.symm_apply_apply,fcFunctionDirection,fcFunctionPairs,List.take_nil,List.headD_cons]
  rfl

/-- The genuinely observed first DC average is exactly FC's first average;
no hypothetical frozen reference replaces the actual measured secant.
Article: main_krylov, s7:N and thm:D. -/
theorem deferredFunctionOperator_zero
    (memory : ℕ → ℕ) (N : ℕ) (hN : N≠1) (estimate : History E → ℝ)
    (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (r : ℝ) (x₀ : E) :
    scalarSearchOnlyOperator (deferredDataMethod memory N estimate) T f G H r x₀ 0=
      metricFCOperator T f G H memory r x₀ 0 := by
  rw [scalarSearchOnlyOperator,metricFCOperator,deferredFunctionPoint_one memory N hN estimate,
    metricFCPoint_zero]
  simp only [scalarFunctionPoint,scalarFunctionRun,History.displacement,List.map_nil,List.sum_nil,add_zero]

end
end krylov.Convergence
