import krylov.Methods.LBFGSCoefficients

set_option autoImplicit false
/-!
Article: main_krylov, cor:lm and s3:cor:qn, actual BFGS/L-BFGS primitive observed rule.
Use: give a concrete true finite observed-vector coefficient rule for
scalar-initialized actual two-loop BFGS/L-BFGS, with genuine primitive domains.
Source: the proved exact real coefficient two-loop synthesis and actual
fixed-shape retained-pair history charts.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference krylov.Stability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- The genuine finite primitive observed coefficient rule for scalar-initialized actual BFGS/L-BFGS.
Use: The genuine finite primitive observed coefficient rule for scalar-initialized actual BFGS/L-BFGS.
Article: main_krylov, cor:lm and s3:cor:qn, actual BFGS/L-BFGS primitive observed rule.
Proof: Run the true two-loop coefficient recursion on the genuine fixed coefficient-history window and current gradient. -/
def lbfgsObservedRule (memory : ℕ → ℕ) (c : ℝ) (shape : List ℕ) (n : ℕ) : ObservedRule E n where
  coefficient data := -inverseBFGSCoefficients data c (selectedWindow memory (coefficientHistory shape n))
    (coefficientHistory shape n).gradient

/-- The genuine finite primitive BFGS/L-BFGS coefficients synthesize exactly the actual raw two-loop direction.
Use: The genuine finite primitive BFGS/L-BFGS coefficients synthesize exactly the actual raw two-loop direction.
Article: main_krylov, cor:lm and s3:cor:qn, actual BFGS/L-BFGS primitive observed rule.
Proof: Use actual coefficient synthesis for the real two-loop recursion and the proved true retained-window and gradient synthesis identities. -/
theorem lbfgsObservedRule_evaluate (memory : ℕ → ℕ) (c : ℝ) (shape : List ℕ)
    (n : ℕ) (data : Fin n → E) :
    (lbfgsObservedRule memory c shape n).evaluate data=
      (lbfgsMethod memory (fun _ => c)).direction (historyFromObservations shape (List.ofFn data)) := by
  change observationSynthesis data (-inverseBFGSCoefficients data c (selectedWindow memory (coefficientHistory shape n))
    (coefficientHistory shape n).gradient)=-inverseBFGSApply c (chartWindow memory shape data) (chartGradient shape data)
  rw [map_neg,inverseBFGSCoefficients_synthesis,chartWindow_synthesis,chartGradient_synthesis]

/-- The actual BFGS/L-BFGS finite primitive observation coefficients are smooth at every order on genuine observed nonzero retained curvature pivots.
Use: The actual BFGS/L-BFGS finite primitive observation coefficients are smooth at every order on genuine observed nonzero retained curvature pivots.
Article: main_krylov, cor:lm and s3:cor:qn, actual BFGS/L-BFGS primitive observed rule.
Proof: Apply the true coefficient recursion regularity and transfer each actual physical pivot through the genuine fixed coefficient-window synthesis. -/
theorem lbfgsObservedRule_regular (memory : ℕ → ℕ) (c : ℝ) (shape : List ℕ)
    (data : Fin n → E) (r : WithTop ℕ∞)
    (hpiv : ∀ p∈chartWindow memory shape data, inner ℝ p.1 p.2≠0) :
    ContDiffAt ℝ r (lbfgsObservedRule memory c shape n).coefficient data := by
  apply ContDiffAt.neg
  apply inverseBFGSCoefficients_regular id (fun _ => c) _
    (fun _ => (coefficientHistory shape n).gradient) data contDiffAt_id contDiffAt_const contDiffAt_const
  intro p hp
  apply hpiv (observationSynthesis data p.1,observationSynthesis data p.2)
  rw [chartWindow_synthesis]
  exact List.mem_map.mpr ⟨p,hp,rfl⟩
end
end krylov.Methods
