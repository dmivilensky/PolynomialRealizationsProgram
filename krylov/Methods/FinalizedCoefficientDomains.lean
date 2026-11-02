import krylov.Methods.FinalizedCompilation

set_option autoImplicit false
/-!
Article: main_krylov, thm:select and apB:lem:mu(a), genuine final-wrapper primitive coefficient domains.
Use: derive the actual finite observed coefficient regularity of the
final latest-model wrapper from true original primitive domains and
real observed full-model determinants, including the genuine later FC branch.
Source: actual appended observed-model regularity, true augmented chart
determinant identity and genuine arbitrary-query-shape FC coefficients.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference krylov.Stability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Before the genuine horizon, actual original primitive coefficient domains and the true full observed augmented-model determinant domain imply real primitive smoothness of the actual compiled final wrapper.
Use: Before the genuine horizon, actual original primitive coefficient domains and the true full observed augmented-model determinant domain imply real primitive smoothness of the actual compiled final wrapper.
Article: main_krylov, thm:select and apB:lem:mu(a), genuine final-wrapper primitive coefficient domains.
Proof: The genuine direction is unchanged; each actual earlier program is the real original primitive program. At the true last iteration apply actual appended-model coefficient regularity and transfer the real full-model determinant through the genuine observed chart. -/
theorem finalizedCompiled_regular_before (P : CompiledProbedPolicy E) (N : ℕ) (reference : ℕ → History E)
    (H : History E) (Q : E →L[ℝ] E) (r : WithTop ℕ∞)
    (hshape : selectedHistoryShape reference H.observationList.length=H.queryShape)
    (hk : H.records.length<N) (hP : P.CoefficientsRegularAt r H Q Q)
    (hM : (windowModel ((P.method.direction H,Q (P.method.direction H))::selectedWindow fullMemory H)).det≠0) :
    (finalizedCompiledPolicy P N reference).CoefficientsRegularAt r H Q Q := by
  -- The actual original primitive direction and genuine reached program domains are retained before applying the real final-model inverse chart.
  have hd := finalizedCompiled_direction_before P N reference H hshape hk
  constructor
  · change ContDiffAt ℝ r ((if (selectedHistoryShape reference H.observationList.length).length<N then
      P.directionRule H.observationList.length else _) : ObservedRule E H.observationList.length).coefficient _
    rw [hshape,show H.queryShape.length=H.records.length by simp only [History.queryShape,List.length_map],ite_eq_left hk]
    exact hP.1
  · change ((if (selectedHistoryShape reference H.observationList.length).length+1=N then _ else if _ then _ else _) : CorrectionProgram E (H.observationList.length+3)).RegularAt r Q _ _
    rw [hshape,show H.queryShape.length=H.records.length by simp only [History.queryShape,List.length_map],hd]
    by_cases he : H.records.length+1=N
    · rw [ite_eq_left he]
      apply appendedModelObserved_regular
      · exact hP.2
      · rw [← augmentedChart_model_det,chartWindow_of_array fullMemory H _ (ofFn_observedArray H.observationList).symm]
        exact hM
    · rw [ite_eq_right he,ite_eq_left hk]
      exact hP.2

/-- After the true horizon, genuine full-window conjugacy nonsingularity implies actual primitive coefficient smoothness of the real compiled final wrapper.
Use: After the true horizon, genuine full-window conjugacy nonsingularity implies actual primitive coefficient smoothness of the real compiled final wrapper.
Article: main_krylov, thm:select and apB:lem:mu(a), genuine final-wrapper primitive coefficient domains.
Proof: Use the actual selected query shape in the genuine FC coefficient chart; the real correction program is empty. -/
theorem finalizedCompiled_regular_after (P : CompiledProbedPolicy E) (N : ℕ) (reference : ℕ → History E)
    (H : History E) (Q : E →L[ℝ] E) (r : WithTop ℕ∞)
    (hshape : selectedHistoryShape reference H.observationList.length=H.queryShape)
    (hk : N≤H.records.length)
    (hC : (crossGram (windowImages (selectedWindow fullMemory H)) (windowSteps (selectedWindow fullMemory H))).det≠0) :
    (finalizedCompiledPolicy P N reference).CoefficientsRegularAt r H Q Q := by
  -- Genuine arbitrary-query-shape FC coefficients use the actual full conjugacy domain after the real final correction has changed the transcript.
  constructor
  · change ContDiffAt ℝ r ((if (selectedHistoryShape reference H.observationList.length).length<N then _
      else fcObservedRule fullMemory (selectedHistoryShape reference H.observationList.length) H.observationList.length)
      : ObservedRule E H.observationList.length).coefficient _
    rw [hshape,show H.queryShape.length=H.records.length by simp only [History.queryShape,List.length_map],ite_eq_right (by omega)]
    exact fcObservedRule_actual_regular fullMemory H _ (ofFn_observedArray H.observationList).symm r hC
  · change ((if (selectedHistoryShape reference H.observationList.length).length+1=N then _ else if _ then _ else _) : CorrectionProgram E (H.observationList.length+3)).RegularAt r Q _ _
    rw [hshape,show H.queryShape.length=H.records.length by simp only [History.queryShape,List.length_map],
      ite_eq_right (by omega),ite_eq_right (by omega)]
    trivial
end
end krylov.Methods
