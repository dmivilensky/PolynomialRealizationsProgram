import krylov.Convergence.ObservableSemantics

/-!
Article: main_krylov, apG:Dunif, literal FC stopping prefix.
Use: extract the true finite searched prefix from the actual observable
cycle, retaining exactly the tests that were passed at earlier nodes.
Source: induction over the executable first-stopping recursion. An early
failure is an output case, never a source nondegeneracy assumption.
-/
namespace krylov.Convergence
noncomputable section
open Matrix krylov.Methods krylov.Functions
open scoped InnerProductSpace
attribute [local instance] Classical.propDecidable
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual search-only observations before imposing the stopping
tests. The returned observable cycle is proved to be a prefix of this
concrete queried history. Article: main_krylov, apG:Dunif. -/
def observableFCSearchRun (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) : ℕ → History E
  | 0 => ⟨G x₀,[]⟩
  | k+1 =>
      let H := observableFCSearchRun T f G r x₀ k
      ⟨H.initial,observableRecord T f G r x₀ H 0 false::H.records⟩

/-- The genuine current physical point of the actual search-only
history. Article: main_krylov, apG:Dunif. -/
def observableFCSearchPoint (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (k : ℕ) : E := x₀+(observableFCSearchRun T f G r x₀ k).displacement

/-- Precisely the observable tests needed to execute another FC search.
This contains no lower gain, reference comparison or convergence bound.
Article: main_krylov, apG:Dunif. -/
def ObservableFCGood (H : History E) : Prop :=
  H.gradient≠0 ∧ IsUnit (crossGram (windowImages (selectedWindow fullMemory H))
    (windowSteps (selectedWindow fullMemory H))).det ∧
      inner ℝ H.gradient (rfcFunctionDirection fullMemory H)<0

/-- Every unconditional searched prefix has its genuine current
gradient, endpoint and exact iteration count. Article: apG:Dunif. -/
theorem observableFCSearchRun_semantics (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (k : ℕ) :
    (observableFCSearchRun T f G r x₀ k).gradient=G (observableFCSearchPoint T f G r x₀ k) ∧
      (observableFCSearchRun T f G r x₀ k).records.length=k := by
  induction k with
  | zero => simp only [observableFCSearchRun,observableFCSearchPoint,History.gradient,
      History.displacement,List.map_nil,List.sum_nil,add_zero,List.length_nil,and_self]
  | succ k ih =>
    refine ⟨observableRecord_append_gradient T f G r x₀ _ 0 false,?_⟩
    simpa only [observableFCSearchRun,List.length_cons] using congrArg Nat.succ ih.2

/-- The literal FC advance either stops at the current observations or
appends its actual searched record. Article: apG:Dunif. -/
theorem observable_fc_advance (bar : ℝ) (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (H : History E) :
    observableRestartAdvance false bar T f G r x₀ H=
      if H.gradient=0 then ⟨H,some .stationary⟩
      else if ¬IsUnit (crossGram (windowImages (selectedWindow fullMemory H))
          (windowSteps (selectedWindow fullMemory H))).det ∨
            ¬inner ℝ H.gradient (rfcFunctionDirection fullMemory H)<0 then ⟨H,some .direction⟩
      else ⟨⟨H.initial,observableRecord T f G r x₀ H 0 false::H.records⟩,none⟩ := by
  simp only [observableRestartAdvance,Bool.false_eq_true, false_and,ite_false]

/-- A literal observable FC cycle ends at an actual searched prefix.
All earlier direction tests passed; the terminal alternative is exactly
horizon, true stationarity or a failed direction test.
Article: main_krylov, apG:Dunif, first-stopping dictionary. -/
theorem observable_fc_cycle_prefix_from (bar : ℝ) (T : E ≃L[ℝ] E)
    (f : E → ℝ) (G : E → E) (r : ℝ) (x₀ : E) (fuel k : ℕ) :
    ∃ K,k≤K ∧ K≤k+fuel ∧
      (observableCycleFrom false bar T f G r x₀ fuel (observableFCSearchRun T f G r x₀ k)).history=
        observableFCSearchRun T f G r x₀ K ∧
      (∀ j,k≤j → j<K → ObservableFCGood (observableFCSearchRun T f G r x₀ j)) ∧
      (K=k+fuel ∨ ¬ObservableFCGood (observableFCSearchRun T f G r x₀ K)) := by
  classical
  induction fuel generalizing k with
  | zero => exact ⟨k,le_rfl,by omega,rfl,by intro j hj hlt;omega,Or.inl (by omega)⟩
  | succ fuel ih =>
    let H := observableFCSearchRun T f G r x₀ k
    by_cases hg : H.gradient=0
    · refine ⟨k,le_rfl,by omega,?_,by intro j hj hlt;omega,Or.inr ?_⟩
      · change (observableCycleFrom false bar T f G r x₀ (fuel+1) H).history=H
        rw [observableCycleFrom,observable_fc_advance,ite_eq_left hg]
        rfl
      · exact fun hh=>hh.1 hg
    · by_cases hb : ¬IsUnit (crossGram (windowImages (selectedWindow fullMemory H))
          (windowSteps (selectedWindow fullMemory H))).det ∨
            ¬inner ℝ H.gradient (rfcFunctionDirection fullMemory H)<0
      · refine ⟨k,le_rfl,by omega,?_,by intro j hj hlt;omega,Or.inr ?_⟩
        · change (observableCycleFrom false bar T f G r x₀ (fuel+1) H).history=H
          rw [observableCycleFrom,observable_fc_advance,ite_eq_right hg,ite_eq_left hb]
          rfl
        · intro hh
          exact hb.elim (fun hu=>hu hh.2.1) (fun hs=>hs hh.2.2)
      · have hgood : ObservableFCGood H := ⟨hg,not_not.mp (not_or.mp hb).1,
          not_not.mp (not_or.mp hb).2⟩
        obtain ⟨K,hk,hK,he,hprev,hend⟩ := ih (k+1)
        refine ⟨K,by omega,by omega,?_,?_,hend.imp (by omega) id⟩
        · change (observableCycleFrom false bar T f G r x₀ (fuel+1) H).history=_
          rw [observableCycleFrom,observable_fc_advance,ite_eq_right hg,ite_eq_right hb]
          exact he
        · intro j hj hlt
          by_cases heq : j=k
          · simpa only [heq] using hgood
          · exact hprev j (by omega) hlt

/-- Every genuine observable FC output has an actual prefix with only
the original observable stopping alternatives. Article: apG:Dunif. -/
theorem observable_fc_cycle_prefix (bar : ℝ) (T : E ≃L[ℝ] E)
    (f : E → ℝ) (G : E → E) (r : ℝ) (x₀ : E) (N : ℕ) :
    ∃ K,K≤N ∧ observableRestartPoint false bar T f G r N x₀=
      observableFCSearchPoint T f G r x₀ K ∧
      (∀ j<K,ObservableFCGood (observableFCSearchRun T f G r x₀ j)) ∧
      (K=N ∨ ¬ObservableFCGood (observableFCSearchRun T f G r x₀ K)) := by
  obtain ⟨K,_hk,hK,he,hgood,hend⟩ := observable_fc_cycle_prefix_from bar T f G r x₀ N 0
  refine ⟨K,by simpa only [Nat.zero_add] using hK,?_,fun j hj=>hgood j (Nat.zero_le _) hj,?_⟩
  · change x₀+(observableCycleFrom false bar T f G r x₀ N (observableFCSearchRun T f G r x₀ 0)).history.displacement=
      x₀+(observableFCSearchRun T f G r x₀ K).displacement
    rw [he]
  · simpa only [Nat.zero_add] using hend

end
end krylov.Convergence
