import krylov.OneGradient.CalibratedNativeRegularity
import krylov.OneGradient.CalibratedDirectionError
import krylov.OneGradient.NativeTrialError
import krylov.Reference.FullCycle
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), general calibrated replay order.
Use: derive the actual quadratic native image error and true terminal
reference zero for arbitrary smoothly calibrated history-only rules.
Source: genuine calibrated replay recursion and exact full CG termination.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Filter Topology Asymptotics krylov.Methods krylov.Reference krylov.Stability
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Both actual calibrated native image errors are quadratic from
primitive operator and observed trial charts, with all domains derived.
Use: the general incoming and launch formulas keep true replay images.
Article: main_krylov, thm:local(a), general native observed-image order.
Proof: S images are their exact queried actions. In D, true calibrated
CG trials and primitive observed charts give the already proved quadratic
replay theorem through its genuine vanishing coefficient recursion. -/
theorem calibrated_native_image_error (directions : Bool)
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (hpre : ∀ i<N,CG.gradient (cgOperator base) g i≠0)
    (hcal : CalibratedTrial trial (cgOperator base) g N)
    (hT : ∀ (directions : Bool) (k : ℕ),k<N → ContDiffAt ℝ 1 (trialCoordinate trial k)
      (oneGradientData (xrfcBasisMethod directions trial) (fun _ => cgOperator base) g k))
    (A : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : ∀ j,ContDiffAt ℝ 1 (fun z => A z j) 0) (hA0 : A 0=fun _ => cgOperator base)
    (k : ℕ) (hk : k≤N) (i : Fin k) :
    (fun z => xrfcNativeImages directions trial (A z) g k i-
      A z (k-1-i.val) (xrfcNativeColumns directions trial (A z) g k i)) =O[𝓝 0] (fun z => ‖z‖^2) := by
  cases directions with
  | false =>
    have hz : (fun _ : X => (0 : EuclideanSpace ℝ (Fin n))) =O[𝓝 0] (fun z => ‖z‖^2) := isBigO_zero _ _
    simpa only [xrfcNativeColumns,xrfcNativeImages,Bool.false_eq_true,ite_false,sub_self] using hz
  | true =>
    have hp := cgOperator_positive base hb
    exact calibrated_direction_image_quadratic trial A hA (cgOperator base) hA0 hp.1 hp.2 g N hpre
      (calibrated_native_reference_nonzero true trial _ hp.1 hp.2 g N hpre hcal)
      (calibrated_native_reference_trial true trial _ hp.1 hp.2 g N hpre hcal) (hT true) _ (by omega)

/-- The actual calibrated full reference terminal gradient is zero.
Use: its true primitive regularity gives first-order incoming errors.
Article: main_krylov, thm:local(a), general actual terminal zero.
Proof: the genuine native reference gradient is CG; full atoms give its
actual termination index. No terminal output identity is assumed. -/
theorem calibrated_native_terminal_zero (directions : Bool)
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hc : referenceAtomCount base hb g=n)
    (hcal : CalibratedTrial trial (cgOperator base) g n) :
    oneGradientGradient (xrfcBasisMethod directions trial) (fun _ => cgOperator base) g n=0 := by
  have hp := cgOperator_positive base hb
  rw [calibrated_native_reference_gradient directions trial _ hp.1 hp.2 g n
    (fun i hi => cg_nonstagnation base hb g i (by omega)) hcal n le_rfl]
  have h := cg_terminates base hb g
  rwa [hc] at h

end
end krylov.OneGradient
