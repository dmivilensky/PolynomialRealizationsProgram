import krylov.OneGradient.ReferenceQuadraticCoefficient
import krylov.OneGradient.CalibratedSourceOutput
import krylov.OneGradient.CalibratedOutputOrder
import krylov.OneGradient.CalibratedErrorRegularity
import krylov.Stability.MovingMetricOrder
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), genuine own-A0 native calibrated formula.
Use: the actual original S/D output has its full source quadratic formula
in its own actual base metric, frame and penultimate reference-error scale.
Source: native computed incoming/output coefficients, derived moving CG
frame calculus, genuine physical output order and actual metric transfer.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Finset Filter Topology Asymptotics krylov.Methods krylov.Reference krylov.Secant
  krylov.Stability krylov.Correction krylov.Envelope
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual implemented calibrated full-cycle S/D output has the
original source second-order formula in its own actual A0 metric and CG
frame, with its true own-base penultimate reference-error norm and actual
measured last relative trial error. The full primitive remainder is cubic.
Use: completes the own-reference version of the genuine calibrated native
output expansion, without assumed moving frames or incoming/output jets.
Article: main_krylov, thm:local(a), actual own-A0 calibrated output formula.
Proof: native source output and true physical output order are derived
from primitive C-one data. The actual measured error is C-one and zero at
reference. Genuine moving source-coefficient freezing and actual inverse
root action each cost cubic order. Add these exact remainders; full actual
reference activity persists, so its true step norm is precisely the
original penultimate canonical reference-error norm. -/
theorem calibrated_native_moving_source_output_cubic (directions : Bool)
    (trial : History (EuclideanSpace ℝ (Fin (n+1))) → ℝ)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1)
    (hcal : CalibratedTrial trial (cgOperator base) g (n+1))
    (hT : ∀ (directions : Bool) (k : ℕ),k<(n+1) → ContDiffAt ℝ 1 (trialCoordinate trial k)
      (oneGradientData (xrfcBasisMethod directions trial) (fun _ => cgOperator base) g k))
    (A : X → ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hA : ∀ j,ContDiffAt ℝ 1 (fun z => A z j) 0)
    (hsym : ∀ z j,(A z j).IsSymm) (hA0 : ∀ j,A 0 j=base)
    (hpos : ∀ᶠ z in 𝓝 (0 : X),(A z 0).PosDef) :
    let m := xrfcBasisMethod directions trial
    let op := fun z j => cgOperator (A z j)
    let B := fun z => A z 0
    let E := fun z => canonicalIncrement (B z) (A z)
    let eps := fun z => xrfcNativeTrialError directions trial (op z) g n
    (fun z => cgOperator (metricRoot (B z))⁻¹
      (m.outputGradient (op z (n+1)) (oneGradientRun m (op z) g (n+1)))+
        ‖cgCanonicalError (B z) g n‖ •
          (staircaseOperator (B z) g (E z) (E z n) (n+1) (freshDefect (B z) g (E z) (n+1))-
            eps z • cgOperator (E z n) (canonicalCGUnitStep (B z) g n)))
        =O[𝓝 0] (fun z => ‖z‖^3) := by
  let m := xrfcBasisMethod directions trial
  let op := fun z j => cgOperator (A z j)
  let out := fun z => m.outputGradient (op z (n+1)) (oneGradientRun m (op z) g (n+1))
  let B := fun z => A z 0
  let eps := fun z => xrfcNativeTrialError directions trial (op z) g n
  have hB0 : B 0=base := hA0 0
  have hcount : referenceAtomCount (B 0) hpos.self_of_nhds g=n+1 := by simpa only [hB0] using hc
  have hop : ∀ j,ContDiffAt ℝ 1 (fun z => op z j) 0 := fun j => matrixOperator_contDiffAt _ 0 (hA j)
  have hop0 : op 0=fun _ => cgOperator base := funext (fun j => congrArg cgOperator (hA0 j))
  have heps : ContDiffAt ℝ 1 eps 0 ∧ eps 0=0 := calibrated_native_error_data directions trial base hb g (n+1)
    (fun i hi => cg_nonstagnation base hb g i (by omega)) hcal hT op hop hop0 n (by omega)
  have hknown : (fun z => cgOperator (metricRoot base)⁻¹ (out z)+
      referenceQuadraticCoefficient base g (A z) (eps z)) =O[𝓝 0] (fun z => ‖z‖^3) := by
    have h := calibrated_source_output_cubic directions trial base hb g hc hcal hT A hA hsym hA0
    apply h.congr_left
    intro z
    rw [terminal_step_error_norm base hb g hc.ge]
    rfl
  have hcoeff : (fun z => referenceQuadraticCoefficient (B z) g (A z) (eps z)-
      referenceQuadraticCoefficient base g (A z) (eps z)) =O[𝓝 0] (fun z => ‖z‖^3) := by
    simpa only [hB0] using referenceQuadraticCoefficient_moving_cubic B (hA 0) hpos g hcount A hA
      (fun j => (hA0 j).trans hB0.symm) eps heps.1 heps.2
  have hmetric : (fun z => cgOperator (metricRoot (B z))⁻¹ (out z)-
      cgOperator (metricRoot base)⁻¹ (out z)) =O[𝓝 0] (fun z => ‖z‖^3) := by
    simpa only [hB0] using moving_inverse_root_action_cubic B (hA 0) hpos out
      (calibrated_native_output_quadratic directions trial base hb g hc hcal hT A hA hsym hA0)
  have hfinal : (fun z => cgOperator (metricRoot (B z))⁻¹ (out z)+
      referenceQuadraticCoefficient (B z) g (A z) (eps z)) =O[𝓝 0] (fun z => ‖z‖^3) := by
    apply ((hknown.add hcoeff).add hmetric).congr_left
    intro z
    change (cgOperator (metricRoot base)⁻¹ (out z)+referenceQuadraticCoefficient base g (A z) (eps z))+
      (referenceQuadraticCoefficient (B z) g (A z) (eps z)-referenceQuadraticCoefficient base g (A z) (eps z))+
      (cgOperator (metricRoot (B z))⁻¹ (out z)-cgOperator (metricRoot base)⁻¹ (out z))=_
    abel
  apply hfinal.congr' ?_ EventuallyEq.rfl
  filter_upwards [moving_reference_full_atoms B (hA 0) hpos g hcount] with z hz
  obtain ⟨hB,hfull⟩ := hz
  let E := canonicalIncrement (B z) (A z)
  let v := staircaseOperator (B z) g E (E n) (n+1) (freshDefect (B z) g E (n+1))-
    eps z • cgOperator (E n) (canonicalCGUnitStep (B z) g n)
  have hscale : ‖canonicalCGStep (B z) g n‖=‖cgCanonicalError (B z) g n‖ :=
    (terminal_step_error_norm (B z) hB g hfull.ge).symm
  have hcoef : referenceQuadraticCoefficient (B z) g (A z) (eps z)=
      ‖cgCanonicalError (B z) g n‖ • v := congrArg (fun s : ℝ => s • v) hscale
  exact congrArg (fun v => cgOperator (metricRoot (B z))⁻¹ (out z)+v) hcoef

end
end krylov.OneGradient
