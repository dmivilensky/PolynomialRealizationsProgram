import krylov.Convergence.ObservableSemantics

/-!
Article: main_krylov, apG:Dunif, finite observable-cycle induction.
Use: verify all branches of the literal first-stopping program by a
mathematical invariant of real observations, then close the horizon case.
Source: structural induction on the executable remaining cycle length.
-/
namespace krylov.Convergence
noncomputable section
open krylov.Methods
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every real non-stopping observable advance appends exactly one
actual record, independently of whether the correction was accepted.
Article: main_krylov, apG:Dunif. -/
theorem observable_advance_running_length (corrections : Bool) (bar : ℝ)
    (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (r : ℝ) (x₀ : E) (H : History E)
    (hrun : ¬(observableRestartAdvance corrections bar T f G r x₀ H).reason.isSome) :
    (observableRestartAdvance corrections bar T f G r x₀ H).history.records.length=H.records.length+1 := by
  classical
  have hor : (observableRestartAdvance corrections bar T f G r x₀ H).reason.isSome ∨
      (observableRestartAdvance corrections bar T f G r x₀ H).history.records.length=H.records.length+1 := by
    dsimp only [observableRestartAdvance]
    split_ifs <;> simp
  exact hor.resolve_left hrun

/-- A proved actual-step invariant and actual terminal estimates imply
the requested property of the literal whole first-stopping cycle.
Article: main_krylov, apG:Dunif, complete branch induction. -/
theorem observable_cycle_invariant (corrections : Bool) (bar : ℝ)
    (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (r : ℝ) (x₀ : E) (N : ℕ)
    (Inv Done : History E → Prop)
    (hstep : ∀ H : History E,H.records.length<N → Inv H →
      let S := observableRestartAdvance corrections bar T f G r x₀ H
      if S.reason.isSome then Done S.history else Inv S.history)
    (hfull : ∀ H : History E,H.records.length=N → Inv H → Done H) :
    ∀ fuel (H : History E),H.records.length+fuel=N → Inv H →
      Done (observableCycleFrom corrections bar T f G r x₀ fuel H).history := by
  classical
  intro fuel
  induction fuel with
  | zero => intro H hN hInv;exact hfull H (by simpa only [Nat.add_zero] using hN) hInv
  | succ fuel ih =>
    intro H hN hInv
    have hstepH := hstep H (by omega) hInv
    let S := observableRestartAdvance corrections bar T f G r x₀ H
    change (if S.reason.isSome then Done S.history else Inv S.history) at hstepH
    by_cases hs : S.reason.isSome
    · change Done (if S.reason.isSome then S else observableCycleFrom corrections bar T f G r x₀ fuel S.history).history
      rw [ite_eq_left hs]
      rw [ite_eq_left hs] at hstepH
      exact hstepH
    · have hlen := observable_advance_running_length corrections bar T f G r x₀ H hs
      change S.history.records.length=H.records.length+1 at hlen
      change Done (if S.reason.isSome then S else observableCycleFrom corrections bar T f G r x₀ fuel S.history).history
      rw [ite_eq_right hs]
      rw [ite_eq_right hs] at hstepH
      exact ih S.history (by omega) hstepH

end
end krylov.Convergence
