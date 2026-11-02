import krylov.Methods.TargetedFinalCorrection
import krylov.Methods.ProbedModelBasis
import krylov.Methods.CorrectionFreeOracles

set_option autoImplicit false
/-!
Article: main_krylov, apB:prop:consist, actual fixed-coordinate targeted output.
Use: identify the genuinely executed target-relative final query with its true fixed finite full-model coordinates and actual FC incoming gradient.
Source: proved genuine whole-model-tree coordinate invariance, actual FC prefix execution and true empty-correction post-search output.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual full observed model query has exactly its genuine fixed-coordinate physical step.
Use: The actual full observed model query has exactly its genuine fixed-coordinate physical step.
Article: main_krylov, apB:prop:consist, actual fixed-coordinate targeted output.
Proof: Read the true first query from the proved actual complete model-tree coordinate identity. -/
theorem latestAfter_step_coordinates (m : ProbedMethod E) (A B : ℕ → E →L[ℝ] E)
    (g : E) (k : ℕ) (v : E) :
    let H := methodRun m A B g k
    let U := ((m.direction H,probedProbe m A B g k)::H.pairs)
    combine (windowSteps U) (modelCoefficients (windowSteps U) (windowModel U) v)=
      combine (probedStepBasis m A B g k)
        (modelCoefficients (probedStepBasis m A B g k)
          (pairModel (probedStepBasis m A B g k) (probedImageBasis m A B g k)) v) := by
  have he := latestAfter_coordinates m A B g k v
  have hu := congrArg (fun p : CorrectionTree E => match p with
    | .done => 0
    | .query u _ => u) he
  exact hu

/-- The genuine target-relative raw terminal output is exactly its true FC terminal gradient plus the actual fixed-coordinate target-model correction.
Use: The genuine target-relative raw terminal output is exactly its true FC terminal gradient plus the actual fixed-coordinate target-model correction.
Article: main_krylov, apB:prop:consist, actual fixed-coordinate targeted output.
Proof: Preserve the real FC prefix, identify its actual searched gradient and transport only the genuine query through true full-model coordinates. -/
theorem targetedFinalMethod_gradient_coordinates (k : ℕ) (target : E)
    (A B : ℕ → E →L[ℝ] E) (g : E) :
    probedGradient (targetedFinalMethod (k+1) target) A B g (k+1)=
      probedGradient (fcMethod fullMemory) A B g (k+1)+
      B k (combine (probedStepBasis (fcMethod fullMemory) A B g k)
        (modelCoefficients (probedStepBasis (fcMethod fullMemory) A B g k)
          (pairModel (probedStepBasis (fcMethod fullMemory) A B g k)
            (probedImageBasis (fcMethod fullMemory) A B g k))
          (probedGradient (fcMethod fullMemory) A B g (k+1)-target))) := by
  -- The actual raw final output uses the genuine FC prefix and its real searched gradient before the target query.
  rw [targetedFinalMethod_gradient_last]
  have hg := correctionFree_gradient_succ (fcMethod fullMemory) (fun _ _ => rfl) A B g k
  change probedGradient (fcMethod fullMemory) A B g (k+1)=
    searchedGradient (methodRun (fcMethod fullMemory) A B g k).gradient
      ((fcMethod fullMemory).direction (methodRun (fcMethod fullMemory) A B g k))
      (probedProbe (fcMethod fullMemory) A B g k) at hg
  dsimp only [probedProbe,probedDirection] at hg
  rw [← hg]
  have hu := latestAfter_step_coordinates (fcMethod fullMemory) A B g k
    (probedGradient (fcMethod fullMemory) A B g (k+1)-target)
  dsimp only [probedProbe,probedDirection] at hu
  rw [hu]
end
end krylov.Methods
