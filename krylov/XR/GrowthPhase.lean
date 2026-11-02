import krylov.XR.MemoryStateInvariants
import krylov.XR.LocalFirstAcceptance
import krylov.XR.QuadraticTerminal
import krylov.Convergence.WindowObservations

/-!
Article: main_krylov, thm:grow, literal clean-phase bookkeeping.
Use: expose the exact update after the independently proved first-trial
acceptance and genuine positive observation. These are transition lemmas,
not assumptions of an execution object. The source theorem supplies their
hypotheses from G1--G4. Source: the displayed XR control flow.
-/

namespace krylov.XR
noncomputable section
open krylov.Methods krylov.Secant
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exact literal search result when the first true trial is accepted. -/
theorem outerSearch_first_accepted (model : State E → ModelResult E)
    (f : E → ℝ) (G : E → E) (sigma : ℝ) (S : State E)
    (haccept : Accepted f sigma S.point S.gradient ((model S).safeDirection S) 1) :
    outerSearch model f G sigma S =
      ⟨(model S).pairs, (model S).bounds, (model S).safeDirection S, 1, 1,
        (model S).pairsBeforeTest, (model S).deletedByTest⟩ := by
  classical
  simp only [outerSearch, ite_eq_left haccept]

/-- The genuine clean update has precisely one newly observed pair and
the printed capacity/counter update, with no hidden rejected probe. -/
theorem outerAdvance_clean_update (P : Parameters) (dimension : ℕ)
    (model : State E → ModelResult E) (f : E → ℝ) (G : E → E) (S : State E)
    (hg : S.gradient ≠ 0)
    (haccept : Accepted f P.armijo S.point S.gradient ((model S).safeDirection S) 1)
    (hpositive : positivePair (observedTrialPair f G S ((model S).safeDirection S))) :
    let u := (model S).safeDirection S
    let S' := outerAdvance P dimension model f G S
    S'.point = S.point + u ∧
      S'.pairs = ((model S).pairs ++ [observedTrialPair f G S u]).map (fun a => a.transport u) ∧
      (S'.capacity, S'.cleanCount) = updateCapacity P dimension S.capacity S.cleanCount
        (model S).pairsBeforeTest (model S).deletedByTest 1 := by
  classical
  rw [outerAdvance, ite_eq_right hg, outerSearch_first_accepted model f G P.armijo S haccept]
  simp only [one_smul]
  rw [appendPositive, ite_eq_left hpositive]
  simp

/-- Full retained memory uses exactly the actual SS1 observed-model query
when values are disabled. No inverse or model approximation is assumed. -/
theorem algorithm_full_ss1Point {n : ℕ} (P : Parameters) (hoff : P.valuesEnabled = false)
    (S : State (EuclideanSpace ℝ (Fin n))) (hn : 0 < n)
    (hfull : (algorithmModel P S).pairs.length = n) :
    S.point + (algorithmModel P S).direction =
      krylov.Convergence.ss1Point (storedSteps (algorithmModel P S).pairs)
        (storedImages (algorithmModel P S).pairs) S.gradient S.point := by
  have hu := algorithmModel_direction_decomposition P S (by omega)
  rw [algorithmTrialParameter_full P S hn hfull, zero_smul, add_zero,
    selectedModel_values_off P hoff] at hu
  rw [hu]
  rfl

end
end krylov.XR
