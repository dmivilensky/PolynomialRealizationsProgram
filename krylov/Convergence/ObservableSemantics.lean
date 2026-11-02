import krylov.Convergence.ObservableRestart

/-!
Article: main_krylov, apG:Dunif, actual observable-cycle semantics.
Use: prove that every returned gradient is the genuine function gradient
at its actual endpoint, and bound the number of actual recorded steps
before any analytic induction. Source: the literal finite restart recursion.
-/
namespace krylov.Convergence
noncomputable section
open krylov.Methods krylov.Functions
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every actual observable record moves to precisely its line endpoint
plus its accepted correction. Article: main_krylov, apG:Dunif. -/
theorem observableRecord_endpoint (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (H : History E) (u : E) (queried : Bool) :
    x₀+H.displacement+(observableRecord T f G r x₀ H u queried).step=
      rfcFunctionLinePoint T f fullMemory r x₀ H+u := by
  simp only [observableRecord,rfcFunctionLineStep]
  abel

/-- Appending the actual record preserves the true observed gradient
dictionary at its literal physical endpoint. Article: apG:Dunif. -/
theorem observableRecord_append_gradient (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (H : History E) (u : E) (queried : Bool) :
    let H' : History E := ⟨H.initial,observableRecord T f G r x₀ H u queried::H.records⟩
    H'.gradient=G (x₀+H'.displacement) := by
  dsimp only
  simp only [History.gradient,History.displacement,List.map_cons,List.sum_cons]
  have he := observableRecord_endpoint T f G r x₀ H u queried
  change G (rfcFunctionLinePoint T f fullMemory r x₀ H+u)=
    G (x₀+((observableRecord T f G r x₀ H u queried).step+H.displacement))
  congr 1
  rw [←he]
  abel

/-- Every branch of the actual observable advance returns the true
gradient, including stopping before a search and rejecting a correction.
Article: main_krylov, apG:Dunif. -/
theorem observableRestartAdvance_gradient (corrections : Bool) (bar : ℝ)
    (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (r : ℝ) (x₀ : E) (H : History E)
    (hH : H.gradient=G (x₀+H.displacement)) :
    let S := observableRestartAdvance corrections bar T f G r x₀ H
    S.history.gradient=G (x₀+S.history.displacement) := by
  dsimp only [observableRestartAdvance]
  split_ifs
  · exact hH
  · exact hH
  · exact observableRecord_append_gradient T f G r x₀ H 0 false
  · exact observableRecord_append_gradient T f G r x₀ H _ true
  · exact observableRecord_append_gradient T f G r x₀ H 0 false

/-- An actual advance appends at most one genuine accepted total step.
Article: main_krylov, apG:Dunif, cycle horizon. -/
theorem observableRestartAdvance_length (corrections : Bool) (bar : ℝ)
    (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (r : ℝ) (x₀ : E) (H : History E) :
    (observableRestartAdvance corrections bar T f G r x₀ H).history.records.length≤H.records.length+1 := by
  dsimp only [observableRestartAdvance]
  split_ifs <;> simp only [List.length_cons] <;> omega

/-- Every recursively returned cycle gradient is genuinely evaluated
at the actual returned point. Article: main_krylov, apG:Dunif. -/
theorem observableCycleFrom_gradient (corrections : Bool) (bar : ℝ)
    (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (r : ℝ) (x₀ : E) (N : ℕ) (H : History E)
    (hH : H.gradient=G (x₀+H.displacement)) :
    let S := observableCycleFrom corrections bar T f G r x₀ N H
    S.history.gradient=G (x₀+S.history.displacement) := by
  induction N generalizing H with
  | zero => exact hH
  | succ N ih =>
    have hs := observableRestartAdvance_gradient corrections bar T f G r x₀ H hH
    dsimp only [observableCycleFrom]
    split
    · exact hs
    · exact ih _ hs

/-- The actual observable cycle never exceeds its prescribed horizon.
Article: main_krylov, apG:Dunif. -/
theorem observableCycleFrom_length (corrections : Bool) (bar : ℝ)
    (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (r : ℝ) (x₀ : E) (N : ℕ) (H : History E) :
    (observableCycleFrom corrections bar T f G r x₀ N H).history.records.length≤H.records.length+N := by
  induction N generalizing H with
  | zero => exact le_rfl
  | succ N ih =>
    have hs := observableRestartAdvance_length corrections bar T f G r x₀ H
    dsimp only [observableCycleFrom]
    split
    · omega
    · have hh := ih (observableRestartAdvance corrections bar T f G r x₀ H).history
      omega

/-- A fresh actual observable cycle returns its true gradient and at
most N accepted total steps. Article: main_krylov, apG:Dunif. -/
theorem observableRestartCycle_semantics (corrections : Bool) (bar : ℝ)
    (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (r : ℝ) (N : ℕ) (x₀ : E) :
    (observableRestartCycle corrections bar T f G r N x₀).history.gradient=
      G (observableRestartPoint corrections bar T f G r N x₀) ∧
      (observableRestartCycle corrections bar T f G r N x₀).history.records.length≤N := by
  refine ⟨observableCycleFrom_gradient corrections bar T f G r x₀ N ⟨G x₀,[]⟩
    (by simp only [History.gradient,History.displacement,List.map_nil,List.sum_nil,add_zero]),?_⟩
  simpa only [observableRestartCycle,List.length_nil,Nat.zero_add] using
    observableCycleFrom_length corrections bar T f G r x₀ N ⟨G x₀,[]⟩

end
end krylov.Convergence
