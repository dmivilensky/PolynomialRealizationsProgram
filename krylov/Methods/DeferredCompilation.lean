import krylov.Methods.DeferredObserved
import krylov.Methods.DeferredReindex
import krylov.Methods.DeferredReference
import krylov.Methods.EmptyCompilation

set_option autoImplicit false
/-!
Article: main_krylov, s3:def:DC and apB:lem:mu(d), actual finite primitive deferred policy compilation.
Use: compile the genuine horizon-selected deferred/FC direction into the
real raw policy and derive primitive coefficient regularity on actual histories.
Source: true fixed query-history reconstruction, genuine observed tilted
coefficient programs and actual finite-list inverse coordinate invariance.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference krylov.Stability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine primitive observed direction rule selects the actual deferred solve only at the prescribed true horizon and real FC otherwise.
Use: The genuine primitive observed direction rule selects the actual deferred solve only at the prescribed true horizon and real FC otherwise.
Article: main_krylov, s3:def:DC and apB:lem:mu(d), actual finite primitive deferred policy compilation.
Proof: The true fixed history shape determines the actual current iteration. -/
def deferredMethodObservedRule (memory : ℕ → ℕ) (N : ℕ) (a : ℝ) (shape : List ℕ) (n : ℕ) : ObservedRule E n :=
  if shape.length+1=N then deferredObservedRule memory shape n a else fcObservedRule memory shape n

/-- The actual primitive finite observed rule evaluates exactly to the genuine deferred raw policy on the true reconstructed full history.
Use: The actual primitive finite observed rule evaluates exactly to the genuine deferred raw policy on the true reconstructed full history.
Article: main_krylov, s3:def:DC and apB:lem:mu(d), actual finite primitive deferred policy compilation.
Proof: Identify the genuine record count and use real observed synthesis and true physical list/array coordinate invariance. -/
theorem deferredMethodObservedRule_evaluate (memory : ℕ → ℕ) (N : ℕ) (a : ℝ)
    (shape : List ℕ) (n : ℕ) (data : Fin n → E) :
    (deferredMethodObservedRule memory N a shape n).evaluate data=
      (deferredMethod memory N a).direction (historyFromObservations shape (List.ofFn data)) := by
  by_cases hc : shape.length+1=N
  · simp only [deferredMethodObservedRule,deferredMethod,historyFromObservations_records_length,hc,ite_true]
    rw [deferredObservedRule_evaluate]
    exact (deferredDirection_getD_array (chartWindow memory shape data) _
      (chartWindow_length memory shape data) (chartGradient shape data) a).symm
  · simp only [deferredMethodObservedRule,deferredMethod,historyFromObservations_records_length,hc,ite_false]
    exact fcObservedRule_evaluate memory shape data

/-- The actual horizon-selected observed coefficient rule is C-r on its genuine retained cross-Gram inverse domain.
Use: The actual horizon-selected observed coefficient rule is C-r on its genuine retained cross-Gram inverse domain.
Article: main_krylov, s3:def:DC and apB:lem:mu(d), actual finite primitive deferred policy compilation.
Proof: Each true locally fixed horizon branch uses the existing actual deferred or FC primitive coefficient calculus. -/
theorem deferredMethodObservedRule_coefficient_regular (memory : ℕ → ℕ) (N : ℕ) (a : ℝ)
    (shape : List ℕ) (n : ℕ) (data : Fin n → E) (r : WithTop ℕ∞)
    (hC : (crossGram (chartImages memory shape data) (chartSteps memory shape data)).det≠0) :
    ContDiffAt ℝ r (deferredMethodObservedRule memory N a shape n).coefficient data := by
  by_cases hc : shape.length+1=N
  · simp only [deferredMethodObservedRule,hc,ite_true]
    exact deferredObservedRule_coefficient_regular memory shape data a hC r
  · simp only [deferredMethodObservedRule,hc,ite_false]
    exact fcObservedRule_coefficient_regular memory shape data hC r

/-- Every genuine actual history with a true nonsingular retained conjugacy matrix gives real primitive C-r deferred direction coefficients.
Use: Every genuine actual history with a true nonsingular retained conjugacy matrix gives real primitive C-r deferred direction coefficients.
Article: main_krylov, s3:def:DC and apB:lem:mu(d), actual finite primitive deferred policy compilation.
Proof: Reconstruct the actual full observed history and transfer its genuine list matrix determinant to the true fixed finite chart before applying the actual primitive regularity theorem. -/
theorem deferredMethodObserved_actual_regular (memory : ℕ → ℕ) (N : ℕ) (a : ℝ)
    (H : History E) (r : WithTop ℕ∞)
    (hC : (crossGram (windowImages (selectedWindow memory H)) (windowSteps (selectedWindow memory H))).det≠0) :
    ContDiffAt ℝ r (deferredMethodObservedRule memory N a H.queryShape H.observationList.length).coefficient
      (observedArray H.observationList.length H.observationList) := by
  -- Recover the real retained window from the genuine full observation array before transferring its actual determinant domain.
  let data := observedArray H.observationList.length H.observationList
  let shape := H.queryShape
  have hW : chartWindow memory shape data=selectedWindow memory H := by
    dsimp only [chartWindow,shape,data]
    rw [ofFn_observedArray,historyFromObservations_actual]
  have hlen : (selectedWindow memory H).length=min (memory shape.length) shape.length := by
    rw [← hW,chartWindow_length]
  have hd : (crossGram (chartImages memory shape data) (chartSteps memory shape data)).det≠0 := by
    change (crossGram (fun i : Fin (min (memory shape.length) shape.length) => ((chartWindow memory shape data).getD i.val (0,0)).2)
      (fun i : Fin (min (memory shape.length) shape.length) => ((chartWindow memory shape data).getD i.val (0,0)).1)).det≠0
    rw [hW,← crossGram_getD_array_det _ _ hlen]
    exact hC
  exact deferredMethodObservedRule_coefficient_regular memory N a shape _ data r hd
end
end krylov.Methods
