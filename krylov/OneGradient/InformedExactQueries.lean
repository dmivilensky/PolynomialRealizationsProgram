import krylov.OneGradient.InformedCalibration
import krylov.OneGradient.TwoQueryInformation
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(c), true known-base two-query calibration.
Use: derive the actual informed query vectors before any unknown increment
acts, rather than assuming a CG-shaped competing trajectory.
Source: exact informed reference trials, genuine virtual/evaluated point
identities and true complete-prefix causality.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Methods krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every genuine evaluated informed point equals its true CG reference
point on the known quadratic operator throughout each active prefix.
Use: the known-base two-dimensional upper construction has exact actual
first/second query locations, before an unknown increment is observed.
Article: main_krylov, thm:local(c), genuine reference evaluated points.
Proof: the original informed trial is the true CG length; the proved
actual evaluated-point identity therefore is the actual CG point recurrence. -/
theorem informed_reference_evaluated (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (N : ℕ)
    (hpre : ∀ i< N,CG.gradient Q g i≠0) (k : ℕ) (hk : k≤ N) :
    (oneGradientRun (xrfcMethod fullMemory (informedTrial Q)) (fun _ => Q) g k).displacement=
      CG.displacement Q g k := by
  cases k with
  | zero => rfl
  | succ k =>
    have ht : ∀ i< N,informedTrial Q (oneGradientRun (xrfcMethod fullMemory (informedTrial Q)) (fun _ => Q) g i)≠0 :=
      fun _ _ => (informed_trial_positive Q _).ne'
    have h := xrfc_full_evaluated (informedTrial Q) Q hQ hpos g N hpre ht k (by omega)
    dsimp only at h
    rw [(informed_trial_step_reference Q hQ hpos g N hpre k (by omega)).2] at h
    exact h.trans (CG.displacement_succ Q g k).symm

/-- Every actual informed evaluated query on the known quadratic reference
is exactly the true CG step, with no trial discrepancy or virtual movement.
Use: original two-query centring observes precisely the unknown increment's
column on the known last CG step, before any asymptotic approximation.
Article: main_krylov, thm:local(c), true calibrated evaluated queries.
Proof: both genuine consecutive evaluated displacements are the actual CG
points; subtract their exact recurrences to identify the true physical step. -/
theorem informed_reference_step (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (N : ℕ)
    (hpre : ∀ i< N,CG.gradient Q g i≠0) (k : ℕ) (hk : k< N) :
    oneGradientStep (xrfcMethod fullMemory (informedTrial Q)) (fun _ => Q) g k=referenceStep Q g k := by
  have hnext := informed_reference_evaluated Q hQ hpos g N hpre (k+1) (by omega)
  have hold := informed_reference_evaluated Q hQ hpos g N hpre k hk.le
  rw [CG.displacement_succ] at hnext
  change oneGradientStep (xrfcMethod fullMemory (informedTrial Q)) (fun _ => Q) g k+
    (oneGradientRun (xrfcMethod fullMemory (informedTrial Q)) (fun _ => Q) g k).displacement=_ at hnext
  rw [hold] at hnext
  exact add_right_cancel (hnext.trans (add_comm _ _))

/-- The actual informed first two queries remain exactly the known CG
steps for every completely arbitrary unknown second segment operator.
Use: the genuine known-base n=2 centring construction reads the exact
observed unknown column, with no smallness, regularity or output premise.
Article: main_krylov, thm:local(c), true known-base two-query geometry.
Proof: the real first query precedes the unknown operator. The entire
first record is common to every second segment, so the original second
decision is the same genuine calibrated reference CG step. -/
theorem informed_two_queries (Q C : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (hpre : ∀ i<2,CG.gradient Q g i≠0) :
    oneGradientStep (xrfcMethod fullMemory (informedTrial Q)) (twoQueryOperators Q C) g 0=referenceStep Q g 0 ∧
    oneGradientStep (xrfcMethod fullMemory (informedTrial Q)) (twoQueryOperators Q C) g 1=referenceStep Q g 1 := by
  constructor
  · exact informed_reference_step Q hQ hpos g 2 hpre 0 (by decide)
  · unfold oneGradientStep
    rw [twoQuery_first_history]
    exact informed_reference_step Q hQ hpos g 2 hpre 1 (by decide)

end
end krylov.OneGradient
