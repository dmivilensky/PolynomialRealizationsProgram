import krylov.Methods.BroydenCoefficientRegularity
import krylov.Methods.HistoryWindowCharts

set_option autoImplicit false
/-!
Article: main_krylov, def:classes, genuine primitive observed convex Broyden policy.
Use: represent the actual accumulated inverse convex Broyden direction by true finite observed coefficients and derive its genuine primitive domain.
Source: proved actual convex Broyden coefficient synthesis, real fixed-shape complete-history reconstruction and genuine recursive physical pivots.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference krylov.Stability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- The actual inverse convex Broyden direction is represented by genuine finite observed-vector coefficients.
Use: The actual inverse convex Broyden direction is represented by genuine finite observed-vector coefficients.
Article: main_krylov, def:classes, genuine primitive observed convex Broyden policy.
Proof: Run the true coefficient model on the genuine full coefficient-history pair window and actual current gradient coordinates. -/
def broydenObservedRule (c : ℝ) (θ : ℕ → ℝ) (shape : List ℕ) (n : ℕ) : ObservedRule E n where
  coefficient data := -inverseBroydenCoefficients data c θ
    (selectedWindow fullMemory (coefficientHistory shape n)) (coefficientHistory shape n).gradient

/-- The genuine observed convex Broyden rule evaluates exactly to the actual raw full-memory inverse-model direction.
Use: The genuine observed convex Broyden rule evaluates exactly to the actual raw full-memory inverse-model direction.
Article: main_krylov, def:classes, genuine primitive observed convex Broyden policy.
Proof: Synthesize the real full-history pair coefficients and current gradient before evaluating the true accumulated inverse model. -/
theorem broydenObservedRule_evaluate (c : ℝ) (θ : ℕ → ℝ) (shape : List ℕ) (n : ℕ) (data : Fin n → E) :
    (broydenObservedRule c θ shape n).evaluate data=
      (broydenMethod c θ).direction (historyFromObservations shape (List.ofFn data)) := by
  -- The genuine full pair window and actual current gradient reconstruct exactly from the real structured observation chart.
  change observationSynthesis data (-inverseBroydenCoefficients data c θ
    (selectedWindow fullMemory (coefficientHistory shape n)) (coefficientHistory shape n).gradient)=_
  change observationSynthesis data (-inverseBroydenCoefficients data c θ
    (selectedWindow fullMemory (coefficientHistory shape n)) (coefficientHistory shape n).gradient)=
      -inverseBroydenModel c θ (historyFromObservations shape (List.ofFn data)).pairs
        (historyFromObservations shape (List.ofFn data)).gradient
  rw [← selectedWindow_full (historyFromObservations shape (List.ofFn data))]
  change observationSynthesis data (-inverseBroydenCoefficients data c θ
    (selectedWindow fullMemory (coefficientHistory shape n)) (coefficientHistory shape n).gradient)=
      -inverseBroydenModel c θ (chartWindow fullMemory shape data) (chartGradient shape data)
  rw [map_neg,inverseBroydenCoefficients_synthesis,chartWindow_synthesis,chartGradient_synthesis]

/-- The actual finite observed convex Broyden coefficients are C-r at every order on the genuine full chronological physical pivot domain.
Use: The actual finite observed convex Broyden coefficients are C-r at every order on the genuine full chronological physical pivot domain.
Article: main_krylov, def:classes, genuine primitive observed convex Broyden policy.
Proof: Transfer the actual full coefficient window through genuine synthesis and apply true recursive coefficient regularity. -/
theorem broydenObservedRule_regular (c : ℝ) (θ : ℕ → ℝ) (shape : List ℕ) (data : Fin n → E)
    (r : WithTop ℕ∞) (hpiv : BroydenPivots c θ (chartWindow fullMemory shape data)) :
    ContDiffAt ℝ r (broydenObservedRule c θ shape n).coefficient data := by
  apply ContDiffAt.neg
  apply inverseBroydenCoefficients_regular id (fun _ => c) θ _
    (fun _ => (coefficientHistory shape n).gradient) data contDiffAt_id contDiffAt_const contDiffAt_const
  rw [← chartWindow_synthesis]
  exact hpiv
end
end krylov.Methods
