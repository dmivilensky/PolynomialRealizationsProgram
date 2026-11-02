import krylov.Methods.ObservationSynthesis
import krylov.Methods.HistoryObservationRegularity
import krylov.Methods.NonlinearCGRegularity

set_option autoImplicit false
/-!
Article: main_krylov, cor:lm and s3:cor:qn, actual nonlinear CG primitive observed coefficients.
Use: express the genuine Hestenes--Stiefel and Hager--Zhang directions
as actual finite observed-vector coefficient combinations.
Source: genuine fixed coefficient-history synthesis and the standard
observed scalar recurrence of the actual nonlinear CG executor.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference krylov.Stability
variable {E : Type*}
section Linear
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual preceding history obtained by removing the newest real iteration record.
Use: The actual preceding history obtained by removing the newest real iteration record.
Article: main_krylov, cor:lm and s3:cor:qn, actual nonlinear CG primitive observed coefficients.
Proof: Keep the genuine initial gradient and the true record tail. -/
def historyTail (H : History E) : History E := ⟨H.initial,H.records.tail⟩

/-- The newest actual recorded direction, with zero for a genuine empty history.
Use: The newest actual recorded direction, with zero for a genuine empty history.
Article: main_krylov, cor:lm and s3:cor:qn, actual nonlinear CG primitive observed coefficients.
Proof: Read the true newest record when present. -/
def historyLastDirection (H : History E) : E := match H.records with
  | [] => 0
  | r::_ => r.direction

/-- The true observed two-term direction recurrence with its supplied real scalar.
Use: The true observed two-term direction recurrence with its supplied real scalar.
Article: main_krylov, cor:lm and s3:cor:qn, actual nonlinear CG primitive observed coefficients.
Proof: Use minus the actual current gradient plus the true newest recorded direction term, or the genuine initial negative gradient. -/
def historyRecurrence (H : History E) (b : ℝ) : E := match H.records with
  | [] => -H.initial
  | r::_ => -r.gradient+b • r.direction

/-- Actual two-term history recurrence commutes with genuine linear observed-vector synthesis.
Use: Actual two-term history recurrence commutes with genuine linear observed-vector synthesis.
Article: main_krylov, cor:lm and s3:cor:qn, actual nonlinear CG primitive observed coefficients.
Proof: Inspect the real record cases and use true linearity of negation, addition and scalar multiplication. -/
theorem historyRecurrence_map {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E →ₗ[ℝ] F) (H : History E) (b : ℝ) :
    historyRecurrence (H.map f) b=f (historyRecurrence H b) := by
  rcases H with ⟨g,records⟩
  cases records <;> simp only [History.map,List.map_nil,List.map_cons,historyRecurrence,
    IterationRecord.map,map_neg,map_add,map_smul]

end Linear
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual nonlinear CG policy direction is exactly its true history recurrence with the genuine observed scalar coefficient.
Use: The actual nonlinear CG policy direction is exactly its true history recurrence with the genuine observed scalar coefficient.
Article: main_krylov, cor:lm and s3:cor:qn, actual nonlinear CG primitive observed coefficients.
Proof: Inspect the actual empty and nonempty record cases. -/
theorem nonlinearCG_direction_recurrence (coefficient : E → E → E → ℝ) (H : History E) :
    (nonlinearCGMethod coefficient).direction H=
      historyRecurrence H (coefficient H.gradient (historyTail H).gradient (historyLastDirection H)) := by
  rcases H with ⟨g,records⟩
  cases records <;> rfl

/-- The genuine finite primitive observed coefficient rule for the actual nonlinear CG scalar recurrence.
Use: The genuine finite primitive observed coefficient rule for the actual nonlinear CG scalar recurrence.
Article: main_krylov, cor:lm and s3:cor:qn, actual nonlinear CG primitive observed coefficients.
Proof: Compute its real scalar from the true reconstructed physical observations, then apply it to the genuine fixed coordinate coefficient history. -/
def nonlinearCGObservedRule (coefficient : E → E → E → ℝ) (shape : List ℕ) (n : ℕ) : ObservedRule E n where
  coefficient data :=
    let H := historyFromObservations shape (List.ofFn data)
    historyRecurrence (coefficientHistory shape n)
      (coefficient H.gradient (historyTail H).gradient (historyLastDirection H))

/-- The genuine primitive finite nonlinear CG coefficient rule synthesizes exactly the actual raw nonlinear CG policy direction.
Use: The genuine primitive finite nonlinear CG coefficient rule synthesizes exactly the actual raw nonlinear CG policy direction.
Article: main_krylov, cor:lm and s3:cor:qn, actual nonlinear CG primitive observed coefficients.
Proof: The real fixed coordinate history synthesizes to the actual reconstructed complete history; true recurrence linearity transfers the genuine scalar combination. -/
theorem nonlinearCGObservedRule_evaluate (coefficient : E → E → E → ℝ) (shape : List ℕ)
    (n : ℕ) (data : Fin n → E) :
    (nonlinearCGObservedRule coefficient shape n).evaluate data=
      (nonlinearCGMethod coefficient).direction (historyFromObservations shape (List.ofFn data)) := by
  rw [nonlinearCG_direction_recurrence]
  have h := historyRecurrence_map (observationSynthesis data) (coefficientHistory shape n)
    (coefficient (historyFromObservations shape (List.ofFn data)).gradient
      (historyTail (historyFromObservations shape (List.ofFn data))).gradient
      (historyLastDirection (historyFromObservations shape (List.ofFn data))))
  rw [coefficientHistory_synthesis] at h
  exact h.symm
end
end krylov.Methods
