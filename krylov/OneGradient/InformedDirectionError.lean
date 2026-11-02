import krylov.OneGradient.CalibratedDirectionError
import krylov.OneGradient.InformedCalibration
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), actual informed direction-image remainder.
Use: the actual history-only informed direction executor has quadratic
replay-image error in the full primitive perturbation parameter.
Source: true informed reference calibration and primitive observed policy
regularity, genuine S/D reference histories and the native quadratic error.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Methods krylov.Reference krylov.Stability
open Filter Topology Asymptotics
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ}

/-- The genuine informed direction-basis executor has quadratic actual
image error from only primitive C-one segment operators in the full
perturbation parameter. All actual trial charts, reference calibration,
inverse domains and nonzero trials are derived for the implemented policy.
Use: closes the known-base direction-image O(omega²) obligation without
supplying policy, coefficient, trajectory or replay-error regularity.
Article: main_krylov, thm:local(a), true informed direction-image order.
Proof: true S/D quadratic histories transfer the actual informed exact
reference trial. The existing primitive informed policy theorem supplies
all C-one native trial charts. Apply the proved native quadratic image
estimate with genuine positive reference domains and original operators. -/
theorem informed_direction_image_quadratic
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (hpre : ∀ i< N,CG.gradient (cgOperator base) g i≠0)
    (A : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : ∀ i,ContDiffAt ℝ 1 (fun z => A z i) 0)
    (hA0 : A 0=fun _ => cgOperator base) (j : ℕ) (hj : j< N) :
    (fun z => xrfcDImageError (informedTrial (cgOperator base)) (A z) g j)
      =O[𝓝 0] (fun z => ‖z‖^2) := by
  let trial := informedTrial (cgOperator base)
  have hp := cgOperator_positive base hb
  have htS : ∀ i< N,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0 :=
    fun _ _ => (informed_trial_positive (cgOperator base) _).ne'
  apply calibrated_direction_image_quadratic trial A hA (cgOperator base) hA0 hp.1 hp.2 g N hpre
    (fun _ _ => (informed_trial_positive (cgOperator base) _).ne') ?_ ?_ j hj
  · intro i hi
    rw [xrfc_quadratic_basis_histories trial (cgOperator base) hp.1 hp.2 g N hpre htS i hi.le]
    exact (informed_trial_step_reference (cgOperator base) hp.1 hp.2 g N hpre i hi).2
  · intro k hk
    exact informed_trial_reference_contDiff true base hb base hb g N hpre k hk 1

end
end krylov.OneGradient
