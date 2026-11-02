import krylov.Methods.SmoothProbedFields
import Mathlib.Data.List.GetD

/-!
Article: main_krylov, thm:C2(c), original finite observed probe histories.
Use: reconstruct the exact full newest-first query direction/image array
from the genuine complete history and current probe, without unknown matrices.
Source: the actual nonanticipating executor and the already proved
chronological finite executed-pair indexing theorem.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every actual raw query direction paired with its genuine measured probe, in the original newest-first history order.
Use: the known-base midpoint policy reads original probe data independently of correction-contaminated stored secants.
Article: main_krylov, thm:C2(c), original observed probe pairs. -/
def History.queryPairs (H : History E) : List (E × E) := H.records.map fun r => (r.direction,r.probe)

/-- The actual complete-history raw query pairs are precisely the genuine chronological direction/probe transcript.
Use: the finite-history midpoint array is connected to the real executed queries rather than an assumed observation record.
Article: main_krylov, thm:C2(c), exact true query transcript.
Proof: every real executor iteration prepends precisely its chosen raw
direction and actual measured line probe, preserving the complete older query list.
-/
theorem methodRun_queryPairs (m : ProbedMethod E) (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    (methodRun m A B g k).queryPairs=executedPairs (probedDirection m A B g) (probedProbe m A B g) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (probedDirection m A B g k,probedProbe m A B g k)::(methodRun m A B g k).queryPairs=_
    rw [ih]
    rfl

/-- The genuine full finite raw query array read only from the current direction/probe and complete actual earlier history.
Use: the data-only midpoint policy remains total on arbitrary histories, with true zero defaults outside the available observed horizon.
Article: main_krylov, thm:C2(c), original finite observed query array. -/
def historyQueryArray (N : ℕ) (H : History E) (d z : E) (i : Fin (N+1)) : E × E :=
  ((d,z)::H.queryPairs).getD i.val (0,0)

/-- The genuine finite-history query array returns exactly the actual real raw direction and measured probe at each original chronological index.
Use: discharge every information-access premise of the actual informed-base terminal policy.
Article: main_krylov, thm:C2(c), exact finite-history to true-query reconstruction.
Proof: the complete observed query list is the true executed-pair list.
The actual finite horizon contains every requested index, so its default
never applies. Existing chronological pair indexing yields the original
iteration N−i without shifting the source's missing oldest slot.
-/
theorem historyQueryArray_run (m : ProbedMethod E) (A B : ℕ → E →L[ℝ] E) (g : E)
    (N : ℕ) (i : Fin (N+1)) :
    historyQueryArray N (methodRun m A B g N) (probedDirection m A B g N) (probedProbe m A B g N) i=
      (probedDirection m A B g (N-i.val),probedProbe m A B g (N-i.val)) := by
  -- The actual executor supplies all N old observations plus the current real probe.
  unfold historyQueryArray
  rw [methodRun_queryPairs]
  change (executedPairs (probedDirection m A B g) (probedProbe m A B g) (N+1)).getD i.val (0,0)=_
  let j : Fin (executedPairs (probedDirection m A B g) (probedProbe m A B g) (N+1)).length :=
    ⟨i.val,by simpa only [executedPairs_length] using i.isLt⟩
  rw [List.getD_eq_get _ (0,0) j]
  simpa only [Nat.add_sub_cancel,j,List.get_eq_getElem] using
    executedPairs_get (probedDirection m A B g) (probedProbe m A B g) (N+1) i.val i.isLt

end
end krylov.Methods
