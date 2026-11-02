import krylov.Methods.ProbedStepBasis

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(d), true complete raw observed-pair window.
Use: locate every actual earlier recorded step/secant pair in the genuine
full retained window with its true chronological index.
Source: proved actual full-history pair execution and genuine newest-first
finite list indexing.
-/

namespace krylov.Methods
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine full retained window of every actual raw policy is exactly its true complete executed step/secant pair list.
Use: The genuine full retained window of every actual raw policy is exactly its true complete executed step/secant pair list.
Article: main_krylov, apB:lem:mu(d), true complete raw observed-pair window.
Proof: The actual pair list has the true iteration length, so the real full take preserves it. -/
theorem fullWindow_methodRun (m : ProbedMethod E) (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    selectedWindow fullMemory (methodRun m A B g k)=executedPairs (probedStep m A B g) (probedSecant m A B g) k := by
  rw [selectedWindow_methodRun]
  exact List.take_of_length_le (by rw [executedPairs_length];exact le_rfl)

/-- Every true earlier executed step/secant pair belongs to the genuine full observed window of the actual raw policy.
Use: Every true earlier executed step/secant pair belongs to the genuine full observed window of the actual raw policy.
Article: main_krylov, apB:lem:mu(d), true complete raw observed-pair window.
Proof: Choose its genuine newest-first age in the real complete executed pair list. -/
theorem probedPair_mem_fullWindow (m : ProbedMethod E) (A B : ℕ → E →L[ℝ] E) (g : E)
    (k i : ℕ) (hi : i<k) :
    (probedStep m A B g i,probedSecant m A B g i)∈selectedWindow fullMemory (methodRun m A B g k) := by
  rw [fullWindow_methodRun]
  apply List.mem_iff_getElem.mpr
  refine ⟨k-1-i,by rw [executedPairs_length];omega,?_⟩
  rw [executedPairs_get _ _ k (k-1-i) (by omega)]
  have he : k-1-(k-1-i)=i := by omega
  rw [he]
end
end krylov.Methods
