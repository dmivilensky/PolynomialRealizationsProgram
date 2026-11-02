import krylov.Functions.EndpointScalarExecution
import krylov.Functions.EndpointValueReaderSpan
import krylov.Functions.EndpointCentreCongruence

/-!
Article: main_krylov, thm:Fplanar, actual endpoint-grounded global output.
Use: identify the actual final queried point of the globally admitted
original method with its concrete endpoint-only correction. Every reader
field is reconstructed from actual stored/current observations; no reader
matching condition, trajectory field or output location is assumed.
Source: direct scalar execution and the proved unconditional reader span.
-/
namespace krylov.Functions
noncomputable section
open krylov.Methods krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The real globally continued original method evaluates exactly the point
chosen from its concrete retained endpoint values and cached gradients.
Its actual query is made after the true scalar exact search and before
observing the new final gradient. All source-reader consistency conditions
are derived internally. Article: main_krylov, thm:Fplanar. -/
theorem OneCorrectionValueMethod.endpoint_global_output {N : ℕ}
    (M : OneCorrectionValueMethod E N) (hN : 0<N) (T : E ≃L[ℝ] E)
    (f : E → ℝ) (G : E → E) (R : ℝ) (x₀ : E) (k : ℕ) (hfinal : k+1=N) :
    let H := scalarFunctionRun M.gradientPolicy T f G R x₀ k
    let x := x₀+H.displacement
    let d := M.gradientPolicy.direction H
    let y := metricLocalExactPoint T f x d R
    let z := (observedLineParameter d (y-x))⁻¹ • (G y-H.gradient)
    scalarFunctionPoint (M.globalMethod hN (endpointValueReader M.gradientPolicy N f x₀))
      T f G R x₀ (k+1)=
      y+observedSpanFinalCorrection hN M.coefficients H
        (endpointValueReader M.gradientPolicy N f x₀ H z) := by
  let H := scalarFunctionRun M.gradientPolicy T f G R x₀ k
  let x := x₀+H.displacement
  let d := M.gradientPolicy.direction H
  let y := metricLocalExactPoint T f x d R
  let z := (observedLineParameter d (y-x))⁻¹ • (G y-H.gradient)
  change scalarFunctionPoint (valueContinuedMethod M.gradientPolicy N
    (fun H z=>observedSpanFinalCorrection hN M.coefficients H
      (endpointValueReader M.gradientPolicy N f x₀ H z))) T f G R x₀ (k+1)=_
  rw [scalarFunctionPoint_valueContinued_final M.gradientPolicy N _ T f G R x₀ k hfinal]
  rw [guardedValueCandidate_observed_rule M.gradientPolicy hN M.coefficients
    (endpointValueReader M.gradientPolicy N f x₀) H z
    (endpointValueReader_final_gradient _ _ _ _ _ _)
    (endpointValueReader_steps_mem _ _ _ _ _ _)]

end
end krylov.Functions
