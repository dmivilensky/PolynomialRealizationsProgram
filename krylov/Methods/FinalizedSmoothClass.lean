import krylov.Methods.FinalizedLocal
import krylov.Methods.FinalizedCoefficientDomains
import krylov.Methods.FinalizedInformation
import krylov.Methods.ScaledReferenceModel

set_option autoImplicit false
/-!
Article: main_krylov, thm:select and apB:lem:mu(a), genuine smooth arbitrary-method final correction class.
Use: prove the actual arbitrary-method final latest-information wrapper
belongs to the full true smooth globally CG-consistent information class
from concrete genuine primitive observed coefficient programs.
Source: actual preserved earlier histories and true local primitive
compilation, real positive full-model domains and genuine later FC charts.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference krylov.Stability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual final latest-information wrapper of every genuine smooth source method has a true primitive C-two representation on every active quadratic cycle, including cycles before and after its real designated horizon.
Use: The actual final latest-information wrapper of every genuine smooth source method has a true primitive C-two representation on every active quadratic cycle, including cycles before and after its real designated horizon.
Article: main_krylov, thm:select and apB:lem:mu(a), genuine smooth arbitrary-method final correction class.
Proof: Choose the genuine original primitive chart on the actual requested cycle. True earlier histories are preserved, deriving real original coefficient and full-model domains. Actual later histories have the genuine CG pair transcript, deriving real full-memory FC domains. Select genuine new query shapes, prove true local whole-tree agreement and transfer every actual primitive domain to the real compiled reference execution. -/
theorem finalizedMethod_smoothCycleAt (M : SmoothProbedClass E) (N : ℕ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (L : ℕ) (hpre : ∀ k<L, CG.gradient Q g k≠0) :
    SmoothProbedCycleAt (finalizedMethod M.policy N) 2 Q g L := by
  -- Start with the genuine original primitive chart on the requested actual cycle, without assuming the final horizon has already been reached.
  obtain ⟨P,hcoef,hlocal⟩ := M.smooth Q hQ hpos g L hpre
  let H := fun k => methodRun (finalizedMethod M.policy N) (fun _ => Q) (fun _ => Q) g k
  let R := finalizedCompiledPolicy P N H
  have hshape (k : ℕ) : selectedHistoryShape H (H k).observationList.length=(H k).queryShape :=
    selectedHistoryShape_actual H (methodRun_observationLength_strictMono _ _ _ _) k
  have hOriginal (k : ℕ) (hk : k≤L) : methodRun M.policy (fun _ => Q) (fun _ => Q) g k=
      methodRun P.method (fun _ => Q) (fun _ => Q) g k :=
    localCompiled_reference_run M.policy P _ _ g k (fun i hi => hlocal i (hi.trans_le hk))
  -- Actual earlier histories equal the true original histories; their genuine local coefficient chart therefore remains valid.
  have hOldLocal (k : ℕ) (hk : k<L) (hn : k<N) :
      LocalCompiledAt M.policy P (H k) (Q (P.method.direction (H k))) := by
    dsimp only [H]
    rw [finalizedMethod_run_before M.policy N _ _ g k hn,hOriginal k hk.le]
    exact hlocal k hk
  have hNewLocal (k : ℕ) (hk : k<L) :
      LocalCompiledAt (finalizedMethod M.policy N) R (H k) (Q (R.method.direction (H k))) := by
    apply finalizedCompiled_local M.policy P N H (H k) _ (hshape k)
    intro hn
    have hn' : k<N := by simpa only [H,methodRun_length] using hn
    rw [finalizedCompiled_direction_before P N H (H k) (hshape k) hn]
    exact hOldLocal k hk hn'
  -- Derive real original and appended-model domains before the horizon, then genuine full-memory FC domains on the actual changed later transcript.
  have hNewRegular (k : ℕ) (hk : k<L) : R.CoefficientsRegularAt 2 (H k) Q Q := by
    by_cases hn : k<N
    · apply finalizedCompiled_regular_before P N H (H k) Q 2 (hshape k) (by simpa only [H,methodRun_length] using hn)
      · dsimp only [H]
        rw [finalizedMethod_run_before M.policy N _ _ g k hn,hOriginal k hk.le]
        exact hcoef k hk
      · have hd := (hOldLocal k hk hn).self.1
        rw [selectedWindow_full,← hd]
        apply ne_of_gt
        apply Matrix.PosDef.det_pos
        dsimp only [H]
        rw [finalizedMethod_run_before M.policy N _ _ g k hn]
        exact (cgConsistent_augmented_model_posDef M.policy M.consistent Q hQ hpos g k
          (fun i hi => hpre i (hi.trans_lt hk)))
    · apply finalizedCompiled_regular_after P N H (H k) Q 2 (hshape k) (by simp only [H,methodRun_length];omega)
      apply ne_of_gt
      apply Matrix.PosDef.det_pos
      rw [selectedWindow_full,cgConsistent_reference_pairs (finalizedMethod M.policy N) (finalizedMethod_consistent M.policy M.consistent N) Q hQ hpos g k]
      have hp := retainedConjugacy_posDef Q hQ hpos g k k (fun i hi => hpre i (hi.trans hk))
      have ht : (referencePairs Q g k).take k=referencePairs Q g k := List.take_of_length_le (by rw [referencePairs_length])
      rw [ht] at hp
      exact hp
  -- Genuine local whole-tree agreement identifies the true raw and compiled histories before transferring actual primitive regularity.
  have hEq (k : ℕ) (hk : k≤L) : H k=methodRun R.method (fun _ => Q) (fun _ => Q) g k :=
    localCompiled_reference_run_of_raw (finalizedMethod M.policy N) R _ _ g k (fun i hi => hNewLocal i (hi.trans_le hk))
  refine ⟨R,?_,?_⟩
  · intro k hk
    rw [← hEq k hk.le]
    exact hNewRegular k hk
  · intro k hk
    rw [← hEq k hk.le]
    exact hNewLocal k hk

/-- The actual arbitrary smooth globally CG-consistent source method followed by one genuine final latest-information correction and real later FC continuation, as a true complete smooth source-class member.
Use: The actual arbitrary smooth globally CG-consistent source method followed by one genuine final latest-information correction and real later FC continuation, as a true complete smooth source-class member.
Article: main_krylov, thm:select and apB:lem:mu(a), genuine smooth arbitrary-method final correction class.
Proof: Combine actual all-history direction and correction-span admissibility, genuine global quadratic CG consistency and the proved true primitive C-two local representation on every active reference cycle. -/
def finalizedSmoothClass (M : SmoothProbedClass E) (N : ℕ) : SmoothProbedClass E where
  memory := fullMemory
  policy := finalizedMethod M.policy N
  admissible := finalizedMethod_spanRestricted M.memory M.policy M.admissible N
  consistent := finalizedMethod_consistent M.policy M.consistent N
  smooth := fun Q hQ hpos g L hpre => finalizedMethod_smoothCycleAt M N Q hQ hpos g L hpre
end
end krylov.Methods
