import krylov.Methods.InformationSpan
import krylov.Information.CentreModel

/-!
Article: main_krylov, thm:centre, preservation of complete adaptive observations.
Use: turn equality of actual oracle actions on the queried subspaces into
equality of genuine method histories, including every intermediate correction.
Source: finite induction on the existing nonanticipating correction executor.
-/

namespace krylov.Information
noncomputable section
open krylov.Methods krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Agreeing oracle actions on every possible query of a correction tree preserve its full execution.
Use: preserve observed gradients and traces, not merely the total displacement.
Article: main_krylov, thm:centre, intermediate correction observations.
Proof: the first actual query receives the same answer, selecting the same
continuation; finite tree induction preserves all subsequent answers and records. -/
theorem corrections_replay (K : Submodule ℝ E) (q : CorrectionTree E)
    (hq : q.InSubspace K) (B C : E →L[ℝ] E)
    (hBC : ∀ u∈K, B u=C u) (g : E) :
    runCorrections q B g=runCorrections q C g := by
  induction q generalizing g with
  | done => rfl
  | query u next ih =>
    simp only [runCorrections,hBC u hq.1]
    rw [ih (g+C u) (hq.2 (g+C u))]

/-- One actual iteration replays under matching probes and matching correction actions.
Use: the twin-scenario proof respects the real history boundary and every query branch.
Article: main_krylov, thm:centre, one nonanticipating induction step.
Proof: the shared actual probe gives the same line search and correction tree;
the tree replay theorem identifies all genuine returned observations. -/
theorem advance_replay (m : ProbedMethod E) (H : History E)
    (A B C D : E →L[ℝ] E) (K : Submodule ℝ E)
    (hprobe : A (m.direction H)=C (m.direction H))
    (hq : (m.correction H (A (m.direction H))).InSubspace K)
    (hBD : ∀ u∈K, B u=D u) :
    methodAdvance m A B H=methodAdvance m C D H := by
  have hr := corrections_replay K (m.correction H (A (m.direction H))) hq B D hBD
    (searchedGradient H.gradient (m.direction H) (A (m.direction H)))
  simp only [methodAdvance,← hprobe]
  rw [hr]

/-- The full actual finite method history replays when each original query receives the same twin answer.
Use: an information-fibre argument can derive equal histories from concrete
operator actions, without assuming the desired transcript equality.
Article: main_krylov, thm:centre, preservation of all observations before the last correction.
Proof: induction uses the already preserved complete past to select the same
direction and finite correction protocol, then replays that actual iteration. -/
theorem run_replay (m : ProbedMethod E) (A B C D : ℕ → E →L[ℝ] E)
    (g : E) (N : ℕ) (K : ℕ → Submodule ℝ E)
    (hprobe : ∀ k<N, let H := methodRun m A B g k
      A k (m.direction H)=C k (m.direction H))
    (hq : ∀ k<N, let H := methodRun m A B g k
      (m.correction H (A k (m.direction H))).InSubspace (K k))
    (hBD : ∀ k<N, ∀ u∈K k, B k u=D k u) :
    methodRun m A B g N=methodRun m C D g N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    -- Both executions choose their next query from exactly the same complete past.
    have hpast := ih (fun k hk => hprobe k (by omega)) (fun k hk => hq k (by omega))
      (fun k hk => hBD k (by omega))
    rw [methodRun,methodRun,← hpast]
    exact advance_replay m _ _ _ _ _ (K N) (hprobe N (by omega)) (hq N (by omega))
      (hBD N (by omega))

end
end krylov.Information
