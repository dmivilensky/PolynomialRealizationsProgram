import krylov.OneGradient.CalibratedStaircase
import krylov.OneGradient.IncomingFreshDictionary
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), original source calibrated output formula.
Use: express the genuine native S/D semantic output in precisely the
existing fresh-defect/staircase notation and actual last relative error.
Source: actual incoming and output cubic theorems, exact genuine native
flag dictionary, and the source staircase's real terminal pivot action.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Stability
open Matrix Filter Topology Asymptotics krylov.Methods krylov.Reference krylov.Secant
  krylov.Correction krylov.Envelope
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual implemented calibrated full-cycle S/D output satisfies the
original source second-order formula, in the known quadratic reference
metric, with a cubic full-parameter remainder. Its fresh defect and
staircase are exactly the existing original objects, its scale is the
true penultimate canonical reference-error norm, and its last error is
the genuine measured native relative trial error.
Use: source estimates and actual source sharpness families apply directly
to the true implemented output, with no assumed incoming/output jet.
Article: main_krylov, thm:local(a), original frozen-reference formula.
Proof: substitute the exact genuine native staircase and fresh-defect
dictionaries into the actual native cubic output theorem. The true last
unit-step action of the source staircase is only the output increment;
the actual terminal-step norm equals the real penultimate error norm. -/
theorem calibrated_source_output_cubic (directions : Bool)
    (trial : History (EuclideanSpace ℝ (Fin (n+1))) → ℝ)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1)
    (hcal : CalibratedTrial trial (cgOperator base) g (n+1))
    (hT : ∀ (directions : Bool) (k : ℕ),k<(n+1) → ContDiffAt ℝ 1 (trialCoordinate trial k)
      (oneGradientData (xrfcBasisMethod directions trial) (fun _ => cgOperator base) g k))
    (A : X → ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hA : ∀ j,ContDiffAt ℝ 1 (fun z => A z j) 0)
    (hsym : ∀ z j,(A z j).IsSymm) (hA0 : ∀ j,A 0 j=base) :
    let m := xrfcBasisMethod directions trial
    let op := fun z k => cgOperator (A z k)
    let E := fun z => canonicalIncrement base (A z)
    let eps := fun z => xrfcNativeTrialError directions trial (op z) g n
    (fun z => cgOperator (metricRoot base)⁻¹
      (m.outputGradient (op z (n+1)) (oneGradientRun m (op z) g (n+1)))+
        ‖cgCanonicalError base g n‖ •
          (staircaseOperator base g (E z) (E z n) (n+1) (freshDefect base g (E z) (n+1))-
            eps z • cgOperator (E z n) (canonicalCGUnitStep base g n)))
        =O[𝓝 0] (fun z => ‖z‖^3) := by
  have h := calibrated_native_output_cubic directions trial base hb g hc hcal hT A hA hsym hA0
  apply h.congr_left
  intro z
  rw [calibrated_native_launch_eq_staircase directions trial base hb g hc hcal A hA0 z,
    informed_incoming_eq_freshDefect base hb g hc (A z),map_sub,map_smul,
    staircase_terminal_unit base hb g hc,terminal_step_error_norm base hb g hc.ge]

end
end krylov.OneGradient
