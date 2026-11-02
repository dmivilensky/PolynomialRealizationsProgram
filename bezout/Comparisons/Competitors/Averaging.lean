import bezout.Comparisons.Competitors.Propagation

/-!
Article: bezout, DFB accelerated averaging configuration.
Use: computes one actual momentum trajectory and its running sum, with exactly
one oracle call per stage; averaging does not rerun the earlier prefixes.
Proof: the cached momentum component is the physical program state and the
fourth vector equals the sum of all iterates already produced.
-/

namespace bezout.Comparisons.Competitors
noncomputable section
open scoped BigOperators
open bezout.Algorithms

/-- Three live momentum registers and one running-sum vector. -/
structure AveragedState (E : Type*) where
  state : RegisterState 3 E
  sum : E

namespace Momentum
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A cached physical execution with its running iterate sum. -/
def averagedPrefix (data : Momentum) (N : ℕ) (oracle : Fin N → E → E)
    (initial : E) : ℕ → AveragedState E
  | 0 => ⟨(data.program N).initialState initial,initial⟩
  | k+1 =>
      let old := data.averagedPrefix N oracle initial k
      if hk : k<N then
        let next := (data.program N).stage oracle ⟨k,hk⟩ old.state
        ⟨next,old.sum+next.vectors 0⟩
      else old

/-- Averaging preserves the one cached physical momentum trajectory. -/
theorem averagedPrefix_state (data : Momentum) (N : ℕ) (oracle : Fin N → E → E)
    (initial : E) (k : ℕ) :
    (data.averagedPrefix N oracle initial k).state =
      (data.program N).runPrefix oracle initial k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [averagedPrefix, RegisterProgram.runPrefix]
    split_ifs <;> simp_all

/-- The fourth physical vector stores exactly x0 through the current iterate. -/
theorem averagedPrefix_sum (data : Momentum) (N : ℕ) (oracle : Fin N → E → E)
    (initial : E) (k : ℕ) (hk : k≤N) :
    (data.averagedPrefix N oracle initial k).sum =
      ∑ j ∈ Finset.range (k+1), ((data.program N).runPrefix oracle initial j).vectors 0 := by
  induction k with
  | zero => simp [averagedPrefix, RegisterProgram.runPrefix, RegisterProgram.initialState, program]
  | succ k ih =>
    rw [averagedPrefix, dite_eq_left (show k<N by omega)]
    change (data.averagedPrefix N oracle initial k).sum +
      ((data.program N).stage oracle ⟨k,by omega⟩
        (data.averagedPrefix N oracle initial k).state).vectors 0 = _
    rw [ih (by omega), Finset.sum_range_succ
      (fun j => ((data.program N).runPrefix oracle initial j).vectors 0) (k+1)]
    congr 1
    rw [data.averagedPrefix_state,
      RegisterProgram.runPrefix.eq_2 (data.program N) oracle initial k,
      dite_eq_left (show k<N by omega)]

/-- The actual accelerated-averaging output after exactly N physical calls. -/
def averagedOutput (data : Momentum) (N : ℕ) (oracle : Fin N → E → E)
    (initial : E) : E := ((N:ℝ)+1)⁻¹ • (data.averagedPrefix N oracle initial N).sum

/-- The cached algorithm returns the literal average in the article. -/
theorem averagedOutput_eq (data : Momentum) (N : ℕ) (oracle : Fin N → E → E)
    (initial : E) :
    data.averagedOutput N oracle initial = ((N:ℝ)+1)⁻¹ •
      ∑ j ∈ Finset.range (N+1), ((data.program N).runPrefix oracle initial j).vectors 0 := by
  rw [averagedOutput, data.averagedPrefix_sum N oracle initial N le_rfl]

/-- The running-sum implementation makes exactly N actual oracle calls. -/
theorem averaged_oracle_calls (data : Momentum) (N : ℕ) (oracle : Fin N → E → E)
    (initial : E) : (data.averagedPrefix N oracle initial N).state.calls=N := by
  rw [data.averagedPrefix_state]
  exact RegisterProgram.run_calls _ _ _

end Momentum

/-- Reindex the remaining states after a fixed physical impulse. -/
theorem sum_shifted_tail {R : Type*} [AddCommMonoid R] (f : ℕ → R) (N s : ℕ) :
    (∑ j ∈ Finset.range (N+1), if s<j then f (j-(s+1)) else 0) =
      ∑ j ∈ Finset.range (N-s), f j := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases hs : s≤N
    · rw [show N+1-s=(N-s)+1 by omega, Finset.sum_range_succ,
        ite_eq_left (show s<N+1 by omega), show N+1-(s+1)=N-s by omega]
    · simp [show ¬s<N+1 by omega, show N-s=0 by omega, show N+1-s=0 by omega]

end
end bezout.Comparisons.Competitors
