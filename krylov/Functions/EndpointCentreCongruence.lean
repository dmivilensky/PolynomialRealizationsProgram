import krylov.Functions.EndpointValueReader

/-!
Article: main_krylov, thm:Fplanar, actual endpoint information sufficiency.
Use: prove that the admitted centre reads only retained scalar values,
cached endpoint gradients and actual steps. Its decision never reads the
rich transcript's whole-line field, so the concrete reader sets it to zero.
Source: explicit endpoint observer and finite coefficient formula.
-/
namespace krylov.Functions
noncomputable section
open krylov.Methods krylov.Tensor.BinaryCubic
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The observable coefficients depend only on the three real endpoint
fields, independently of points or complete line-objective functions.
Article: main_krylov, thm:Fplanar. -/
theorem metricPlaneCentreData_endpoint_congr {N : ℕ} (S : E ≃L[ℝ] E) (hN : 0<N)
    (a b : FunctionSearchTranscript E N) (hs : a.lineSteps=b.lineSteps)
    (hv : a.values=b.values) (hg : a.gradients=b.gradients) :
    metricPlaneCentreData S hN a=metricPlaneCentreData S hN b := by
  simp only [metricPlaneCentreData,metricPlaneObservedBinaryData,observedPairDefect,
    observedFinalGradient,hs,hv,hg]

/-- Every actual centre correction coefficient is endpoint-only; the
whole-line oracle supplied for the stronger lower class is unused.
Article: main_krylov, thm:Fplanar. -/
theorem metricPlaneResponseCoefficients_endpoint_congr
    (response : ℝ → ℝ → Observation → Plane) {N : ℕ} (S : E ≃L[ℝ] E) (hN : 0<N)
    (H : History E) (a b : FunctionSearchTranscript E N) (hs : a.lineSteps=b.lineSteps)
    (hv : a.values=b.values) (hg : a.gradients=b.gradients) :
    metricPlaneResponseCoefficients response S hN H a=metricPlaneResponseCoefficients response S hN H b := by
  funext i
  unfold metricPlaneResponseCoefficients
  rw [hs,metricPlaneCentreData_endpoint_congr S hN a b hs hv hg]

/-- Equal actual endpoint observations give exactly the same selected
physical correction, without accessing whole line objectives.
Article: main_krylov, thm:Fplanar. -/
theorem metricPlaneResponseCorrection_endpoint_congr
    (response : ℝ → ℝ → Observation → Plane) {N : ℕ} (S : E ≃L[ℝ] E) (hN : 0<N)
    (H : History E) (a b : FunctionSearchTranscript E N) (hs : a.lineSteps=b.lineSteps)
    (hv : a.values=b.values) (hg : a.gradients=b.gradients) :
    observedSpanFinalCorrection hN (metricPlaneResponseCoefficients response S hN) H a=
      observedSpanFinalCorrection hN (metricPlaneResponseCoefficients response S hN) H b := by
  classical
  unfold observedSpanFinalCorrection observedFinalGradient
  rw [hs,hg,metricPlaneResponseCoefficients_endpoint_congr response S hN H a b hs hv hg]

end
end krylov.Functions
