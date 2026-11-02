import krylov.Methods.NonlinearCGObserved

set_option autoImplicit false
/-!
Article: main_krylov, cor:lm and s3:cor:qn, actual nonlinear CG observed coefficient domains.
Use: prove genuine finite primitive HS and HZ coefficient regularity
from true reconstructed current and previous gradients and direction.
Source: actual finite-list observation calculus and the standard
HS/HZ scalar rules on their genuine nonzero observed denominator domain.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference krylov.Stability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ} {r : WithTop ℕ∞}

/-- A regular actual scalar recurrence produces regular genuine finite observed direction coefficients; the empty-history rule is constant.
Use: A regular actual scalar recurrence produces regular genuine finite observed direction coefficients; the empty-history rule is constant.
Article: main_krylov, cor:lm and s3:cor:qn, actual nonlinear CG observed coefficient domains.
Proof: The true fixed coefficient history has constant vector coordinates. On a real nonempty shape only its genuine observed scalar varies. -/
theorem nonlinearCGObservedRule_regular (coefficient : E → E → E → ℝ) (shape : List ℕ)
    (data : Fin n → E)
    (hcoef : shape≠[] → ContDiffAt ℝ r (fun v : Fin n → E =>
      let H := historyFromObservations shape (List.ofFn v)
      coefficient H.gradient (historyTail H).gradient (historyLastDirection H)) data) :
    ContDiffAt ℝ r (nonlinearCGObservedRule coefficient shape n).coefficient data := by
  -- The empty history has constant coefficients; a nonempty shape varies only through its actual observed scalar recurrence.
  cases shape with
  | nil => exact contDiffAt_const
  | cons q qs =>
    change ContDiffAt ℝ r (fun v => -((List.ofFn fun i : Fin n => (Pi.single i 1 : Fin n → ℝ)).drop 2).getD 3 0+
      (coefficient (historyFromObservations (q::qs) (List.ofFn v)).gradient
        (historyTail (historyFromObservations (q::qs) (List.ofFn v))).gradient
        (historyLastDirection (historyFromObservations (q::qs) (List.ofFn v)))) •
      ((List.ofFn fun i : Fin n => (Pi.single i 1 : Fin n → ℝ)).drop 2).getD 0 0) data
    exact contDiffAt_const.add ((hcoef (List.cons_ne_nil _ _)).smul contDiffAt_const)

/-- The actual current gradient, preceding gradient and newest direction have genuine smooth finite observed-data charts at every order.
Use: The actual current gradient, preceding gradient and newest direction have genuine smooth finite observed-data charts at every order.
Article: main_krylov, cor:lm and s3:cor:qn, actual nonlinear CG observed coefficient domains.
Proof: Use the true structured-history gradient chart, the real dropped observation tail for the preceding history, and the genuine latest-direction coordinate. -/
theorem nonlinearCG_history_charts (q : ℕ) (qs : List ℕ) (data : Fin n → E) :
    ContDiffAt ℝ r (fun v : Fin n → E => (historyFromObservations (q::qs) (List.ofFn v)).gradient) data ∧
    ContDiffAt ℝ r (fun v : Fin n → E => (historyTail (historyFromObservations (q::qs) (List.ofFn v))).gradient) data ∧
    ContDiffAt ℝ r (fun v : Fin n → E => historyLastDirection (historyFromObservations (q::qs) (List.ofFn v))) data := by
  have hv : SmoothListAt r (fun v : Fin n → E => List.ofFn v) data :=
    ⟨n,id,contDiffAt_id,Filter.Eventually.of_forall (fun _ => rfl)⟩
  refine ⟨(historyFromObservations_pairs_regular (q::qs) _ data hv).2,?_,?_⟩
  · exact (readHistoryPairs_regular qs (fun v : Fin n → E => (List.ofFn v).getD 1 0)
      (fun v => ((List.ofFn v).drop 2).drop (4+2*q)) data (hv.getD 1) ((hv.drop 2).drop (4+2*q))).2
  · exact (hv.drop 2).getD 0

/-- The actual Hestenes--Stiefel finite primitive direction coefficients are smooth at every order on the true observed denominator domain.
Use: The actual Hestenes--Stiefel finite primitive direction coefficients are smooth at every order on the true observed denominator domain.
Article: main_krylov, cor:lm and s3:cor:qn, actual nonlinear CG observed coefficient domains.
Proof: Compose the genuine HS scalar regularity with all three actual structured-history observation charts and use the true fixed coefficient recurrence. -/
theorem hsObservedRule_regular (shape : List ℕ) (data : Fin n → E)
    (hden : shape≠[] → let H := historyFromObservations shape (List.ofFn data)
      inner ℝ (historyLastDirection H) (H.gradient-(historyTail H).gradient)≠0) :
    ContDiffAt ℝ r (nonlinearCGObservedRule hsCoefficient shape n).coefficient data := by
  apply nonlinearCGObservedRule_regular
  cases shape with
  | nil => intro hz;exact (hz rfl).elim
  | cons q qs =>
    intro _
    have hc := nonlinearCG_history_charts (r := r) q qs data
    exact hsCoefficient_contDiffAt _ _ _ data hc.1 hc.2.1 hc.2.2 (hden (List.cons_ne_nil _ _))

/-- The actual Hager--Zhang finite primitive direction coefficients are smooth at every order on the true observed denominator domain.
Use: The actual Hager--Zhang finite primitive direction coefficients are smooth at every order on the true observed denominator domain.
Article: main_krylov, cor:lm and s3:cor:qn, actual nonlinear CG observed coefficient domains.
Proof: Compose the genuine HZ scalar regularity with the actual observed gradient and direction charts and use the true fixed coefficient recurrence. -/
theorem hzObservedRule_regular (shape : List ℕ) (data : Fin n → E)
    (hden : shape≠[] → let H := historyFromObservations shape (List.ofFn data)
      inner ℝ (historyLastDirection H) (H.gradient-(historyTail H).gradient)≠0) :
    ContDiffAt ℝ r (nonlinearCGObservedRule hzCoefficient shape n).coefficient data := by
  apply nonlinearCGObservedRule_regular
  cases shape with
  | nil => intro hz;exact (hz rfl).elim
  | cons q qs =>
    intro _
    have hc := nonlinearCG_history_charts (r := r) q qs data
    exact hzCoefficient_contDiffAt _ _ _ data hc.1 hc.2.1 hc.2.2 (hden (List.cons_ne_nil _ _))
end
end krylov.Methods
