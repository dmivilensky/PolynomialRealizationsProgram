import krylov.Functions.BudgetedPlaneCentre
import krylov.Methods.InformationSpan

/-!
Article: main_krylov, def:classes(M^F) and thm:Fplanar, admitted centre method.
Use: package a genuine gradient-only globally CG-consistent prefix with
at most one correction per iteration, followed by a single data-only
retained-span value correction. Source: the original causal scalar executor
and the derived all-quadratic zero-correction guard.
-/
namespace krylov.Functions
noncomputable section
open krylov.Methods krylov.Reference krylov.Nonlinear krylov.Tensor.BinaryCubic
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An original finite correction tree has at most one actual query.
Article: main_krylov, definition of M^F. -/
def CorrectionTree.AtMostOne : CorrectionTree E → Prop
  | .done => True
  | .query _ next => ∀ g,next g=.done

/-- Data-only original one-correction value methods. The prefix receives
no values, the final coefficients receive only the retained actual data,
and the output is evaluated by exactly one genuine final gradient query.
Global quadratic zero behaviour of the final guard is proved below,
independently of these coefficient decisions. Article: def:classes(M^F). -/
structure OneCorrectionValueMethod (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (N : ℕ) where
  /-- Original causal gradient-only prefix policy. -/
  gradientPolicy : ProbedMethod E
  /-- Genuine global consistency of that original prefix. -/
  consistent : CGConsistent gradientPolicy
  /-- Original full-memory direction and correction information spans. -/
  admissible : ProbedSpanRestricted fullMemory gradientPolicy
  /-- At most one genuine prefix correction query per iteration. -/
  prefix_one : ∀ H z,CorrectionTree.AtMostOne (gradientPolicy.correction H z)
  /-- Arbitrary coefficients using only retained actual scalar data. -/
  coefficients : History E → FunctionSearchTranscript E N → Fin N → ℝ

/-- The real physical output of the original value method, selected before
the one final gradient query. Article: main_krylov, thm:Fplanar. -/
def OneCorrectionValueMethod.output [CompleteSpace E] {N : ℕ}
    (M : OneCorrectionValueMethod E N) (hN : 0<N) (T : E ≃L[ℝ] E)
    (f : E → ℝ) (R : ℝ) (x₀ : E) : E :=
  scalarValueFinalOutput M.gradientPolicy T f R x₀ N (observedSpanFinalPolicy hN M.coefficients)

/-- The actual final correction remains in the original retained step
span for every possible observed source. Article: def:classes(M^F). -/
theorem OneCorrectionValueMethod.final_mem {N : ℕ} (M : OneCorrectionValueMethod E N)
    (hN : 0<N) (H : History E) (data : FunctionSearchTranscript E N) :
    observedSpanFinalCorrection hN M.coefficients H data∈Submodule.span ℝ (Set.range data.lineSteps) :=
  observedSpanFinalCorrection_mem hN M.coefficients H data

/-- The final tree has at most one actual gradient evaluation, uniformly
in the scalar values and all coefficient choices. Article: thm:Fplanar. -/
theorem OneCorrectionValueMethod.final_one {N : ℕ} (M : OneCorrectionValueMethod E N)
    (hN : 0<N) (H : History E) (data : FunctionSearchTranscript E N) :
    CorrectionTree.AtMostOne (observedSpanFinalTree hN M.coefficients H data) := fun _=>rfl

/-- Every positive quadratic gets zero final movement, from its genuine
gradient formula and true CG orthogonality. No quadratic behaviour is
assumed of the scalar-value decision coefficients.
Article: main_krylov, thm:Fplanar, global quadratic admission. -/
theorem OneCorrectionValueMethod.quadratic_final [CompleteSpace E] {N : ℕ}
    (M : OneCorrectionValueMethod E N) (hN : 0<N) (H : History E)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (f : E → ℝ) (hG : ∀ x,gradient f x=g+Q x) :
    observedSpanFinalPolicy hN M.coefficients H
      (functionSearchTranscript f (CG.displacement Q g) (referenceStep Q g) N)=CG.displacement Q g N := by
  have hg : observedFinalGradient
      (functionSearchTranscript f (CG.displacement Q g) (referenceStep Q g) N)=CG.gradient Q g N := by
    change gradient f (CG.displacement Q g N)=_
    rw [hG,CG.gradient_displacement]
  have hz := observedSpanFinalCorrection_quadratic_zero hN M.coefficients H
    (functionSearchTranscript f (CG.displacement Q g) (referenceStep Q g) N) Q hQ hpos g hg rfl
  rw [observedSpanFinalPolicy,hz,add_zero]
  rfl

variable [CompleteSpace E]

/-- The genuine value-centre method: an ordinary data-only full-memory FC prefix with
empty corrections and the explicit endpoint-only budgeted centre as its
single final retained-span correction. Article: main_krylov, thm:Fplanar. -/
def budgetedCentreValueMethod {N : ℕ} (S : E ≃L[ℝ] E) (B : ℝ) (hN : 0<N) :
    OneCorrectionValueMethod E N :=
  ⟨fcMethod fullMemory,fullFC_consistent,fcMethod_spanRestricted fullMemory,fun _ _=>True.intro,
    metricPlaneResponseCoefficients (budgetedPlaneCentreOutput B) S hN⟩

end
end krylov.Functions
