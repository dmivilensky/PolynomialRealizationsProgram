import krylov.Methods.XRFCBasisHistory
import krylov.Stability.TrialCoordinates

/-!
Article: main_krylov, thm:V, primitive trial-data dictionary in both bases.
Use: identify the actual finite observed coordinates of the two genuine
quadratic executions, and transfer original positive smooth trial charts
between them without a separate step-basis regularity assumption.
Source: equality of complete real quadratic histories and the injective
fixed finite one-gradient observation chart.
-/
namespace krylov.Convergence
noncomputable section
open krylov.Methods krylov.Reference krylov.Stability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
/-- A fixed finite actual observation chart loses none of its initial,
queried-step or returned-gradient data. Article: lem:U, thm:V. -/
theorem oneGradientHistoryChart_injective (k : ℕ) :
    Function.Injective (oneGradientHistoryChart (E:=E) (k:=k)) := by
  intro x y h
  have hi:=congrArg History.initial h
  have hr:=congrArg History.records h
  change x.1=y.1 at hi
  change List.ofFn (fun i : Fin k=>(⟨0,0,x.2.1 i,x.2.2 i,[]⟩ : IterationRecord E))=
    List.ofFn (fun i : Fin k=>(⟨0,0,y.2.1 i,y.2.2 i,[]⟩ : IterationRecord E)) at hr
  have hf:=List.ofFn_injective hr
  apply Prod.ext hi
  apply Prod.ext
  · exact funext fun i=>congrArg IterationRecord.step (congrFun hf i)
  · exact funext fun i=>congrArg IterationRecord.gradient (congrFun hf i)

/-- Equality of genuine complete histories identifies the original
primitive finite trial data exactly. Article: thm:V. -/
theorem oneGradientData_eq_of_run_eq
    (m₁ m₂ : OneGradientMethod E) (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ)
    (h : oneGradientRun m₁ A g k=oneGradientRun m₂ B g k) :
    oneGradientData m₁ A g k=oneGradientData m₂ B g k := by
  apply oneGradientHistoryChart_injective k
  calc
    _ = oneGradientRun m₁ A g k := (oneGradientRun_chart m₁ A g k).symm
    _ = oneGradientRun m₂ B g k := h
    _ = _ := oneGradientRun_chart m₂ B g k

/-- Primitive direction-basis trial domains suffice for exact equality
of the actual finite observed trial coordinates in both reference runs.
Article: main_krylov, thm:V, original direction-basis hypotheses. -/
theorem xrfc_reference_trial_data_of_direction
    (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _=>Q) g i)≠0)
    (k : ℕ) (hk : k≤N) :
    oneGradientData (xrfcDMethod fullMemory trial) (fun _=>Q) g k=
      oneGradientData (xrfcMethod fullMemory trial) (fun _=>Q) g k :=
  oneGradientData_eq_of_run_eq _ _ _ _ _ _
    (xrfc_quadratic_basis_histories_of_direction trial Q hQ hpos g N hpre ht k hk)

/-- Positive smooth primitive trial charts on the actual direction-basis
reference imply precisely the step-basis assumptions used by the shared
coefficient envelope, with no extra source regularity premise.
Article: main_krylov, thm:V, both-basis near-exact cubic transfer. -/
theorem xrfc_reference_trial_dictionary_of_direction
    (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,0<trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _=>Q) g i))
    (r : WithTop ℕ∞)
    (hT : ∀ i<N,ContDiffAt ℝ r (trialCoordinate trial i)
      (oneGradientData (xrfcDMethod fullMemory trial) (fun _=>Q) g i)) :
    (∀ i<N,0<trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _=>Q) g i)) ∧
      ∀ i<N,ContDiffAt ℝ r (trialCoordinate trial i)
        (oneGradientData (xrfcMethod fullMemory trial) (fun _=>Q) g i) := by
  constructor
  · intro i hi
    rw [←xrfc_quadratic_basis_histories_of_direction trial Q hQ hpos g N hpre
      (fun j hj=>(ht j hj).ne') i hi.le]
    exact ht i hi
  · intro i hi
    rw [←xrfc_reference_trial_data_of_direction trial Q hQ hpos g N hpre
      (fun j hj=>(ht j hj).ne') i hi.le]
    exact hT i hi

end
end krylov.Convergence
