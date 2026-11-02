import krylov.Methods.TargetedCompilation
import krylov.Methods.FCSmoothClass

set_option autoImplicit false
/-!
Article: main_krylov, apB:prop:consist, actual targeted primitive coefficient domains.
Use: derive true primitive coefficient regularity of the genuine targeted policy from its actual full-window reference matrices.
Source: genuine FC observed coefficient calculus, actual target-relative program regularity and the true augmented chart/model determinant identity.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference krylov.Stability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine targeted primitive coefficients are C-r at every true zero-query-prefix history with actual nonsingular conjugacy and full augmented models.
Use: The genuine targeted primitive coefficients are C-r at every true zero-query-prefix history with actual nonsingular conjugacy and full augmented models.
Article: main_krylov, apB:prop:consist, actual targeted primitive coefficient domains.
Proof: Retain the genuine FC direction domain; the actual final branch uses the true targeted observed model inverse and every earlier branch is empty. -/
theorem targetedCompiled_coefficients_regular (N : ℕ) (target : E) (H : History E)
    (hshape : H.queryShape=List.replicate H.records.length 0) (r : WithTop ℕ∞) (Q : E →L[ℝ] E)
    (hC : (crossGram (windowImages (selectedWindow fullMemory H)) (windowSteps (selectedWindow fullMemory H))).det≠0)
    (hM : (windowModel (((fcMethod fullMemory).direction H,Q ((fcMethod fullMemory).direction H))::
      selectedWindow fullMemory H)).det≠0) :
    (targetedCompiledPolicy N target).CoefficientsRegularAt r H Q Q := by
  -- Derive the actual branch and coefficient domains from genuine observed history counts and real model determinants.
  have hd := targetedCompiled_direction N target H hshape
  have hdiv : (H.observationList.length-2)/4=H.records.length := by
    have hh := zeroQuery_observationLength H hshape
    omega
  constructor
  · exact (fcCompiled_coefficients_regular fullMemory H hshape r Q Q hC).1
  · change ((if (H.observationList.length-2)/4+1=N then _ else .done) :
      CorrectionProgram E (H.observationList.length+3)).RegularAt r Q _ _
    rw [hdiv,hd]
    by_cases he : H.records.length+1=N
    · rw [ite_eq_left he]
      apply targetedObservedProgram_regular
      rw [← hshape,← augmentedChart_model_det,
        chartWindow_of_array fullMemory H _ (ofFn_observedArray H.observationList).symm]
      exact hM
    · rw [ite_eq_right he]
      trivial
end
end krylov.Methods
