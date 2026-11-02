import krylov.OneGradient.CalibratedNativeReference
import krylov.Stability.TrialCoordinates
import krylov.OneGradient.InformedCalibration
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), fixed known-reference CG trials.
Use: instantiate the general calibrated history-only theory with the
literal known CG lengths, with primitive charts of every real order.
Source: actual observed history count and true constant finite charts.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability
variable {n : ℕ}

/-- The original fixed known-reference CG length rule reads only its
actual observed iteration count and the known reference CG data.
Use: no current unknown operator enters the fixed-trial policy.
Article: main_krylov, thm:local(a), tau_k=alpha_k(A). -/
def fixedCGTrial (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) :
    History (EuclideanSpace ℝ (Fin n)) → ℝ :=
  fun H => CG.length (cgOperator base) g H.records.length

/-- The fixed CG rule uses its actual genuine observed iteration count.
Use: true reference calibration is derived from the real executor.
Article: main_krylov, thm:local(a).
Proof: every true one-gradient run records exactly its actual query count. -/
theorem fixedCGTrial_run (base : Matrix (Fin n) (Fin n) ℝ) (g h : EuclideanSpace ℝ (Fin n))
    (m : OneGradientMethod (EuclideanSpace ℝ (Fin n)))
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    fixedCGTrial base g (oneGradientRun m A h k)=CG.length (cgOperator base) g k := by
  simp only [fixedCGTrial,oneGradientRun_length]

/-- Fixed known-reference CG trials have primitive observed charts of
every differentiability order, at every actual finite input.
Use: the general output theorem's trial smoothness premise is discharged.
Article: main_krylov, thm:local(a).
Proof: the genuine chart has fixed record count, so its coefficient is
literally the corresponding true fixed known CG length. -/
theorem fixedCGTrial_contDiff {r : WithTop ℕ∞} (base : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    ContDiff ℝ r (trialCoordinate (fixedCGTrial base g) k) := by
  change ContDiff ℝ r (fun data => CG.length (cgOperator base) g (oneGradientHistoryChart data).records.length)
  simpa only [oneGradientHistoryChart,List.length_ofFn] using
    (contDiff_const : ContDiff ℝ r (fun _ : EuclideanSpace ℝ (Fin n) ×
      (Fin k → EuclideanSpace ℝ (Fin n)) × (Fin k → EuclideanSpace ℝ (Fin n)) => CG.length (cgOperator base) g k))

/-- The literal fixed known-reference CG rule is genuinely calibrated
on every actual known quadratic prefix.
Use: its general native output formula requires no supplied trial-error jet.
Article: main_krylov, thm:local(a).
Proof: the actual recorded query count gives its prescribed true CG length. -/
theorem fixedCGTrial_calibrated (base : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) :
    CalibratedTrial (fixedCGTrial base g) (cgOperator base) g N :=
  fun k _ => fixedCGTrial_run base g g _ _ k

/-- The genuine informed policy is an instance of the general primitive
calibrated-trial class at its actual known quadratic reference.
Use: informed and fixed-length source formulas share the same general engine.
Article: main_krylov, thm:local(a).
Proof: reuse the real informed trial calibration on each active prefix. -/
theorem informedTrial_calibrated (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (hpre : ∀ i<N,CG.gradient (cgOperator base) g i≠0) :
    CalibratedTrial (informedTrial (cgOperator base)) (cgOperator base) g N := by
  have hp := cgOperator_positive base hb
  exact fun k hk => (informed_trial_step_reference _ hp.1 hp.2 g N hpre k hk).2

end
end krylov.OneGradient
