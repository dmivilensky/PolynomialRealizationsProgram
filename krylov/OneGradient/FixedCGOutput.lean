import krylov.OneGradient.CalibratedMovingOutput
import krylov.OneGradient.FixedCGTrial
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), full fixed-known-CG native output.
Use: literal fixed known CG lengths have the original own-A0 output
formula in both native implementations, with every trial premise derived.
Source: actual fixed policy calibration, constant observed charts and the
shared complete general calibrated native cubic output theorem.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Filter Topology Asymptotics krylov.Methods krylov.Reference krylov.Secant
  krylov.Stability krylov.Correction krylov.Envelope
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Actual fixed known-CG trials satisfy the complete original own-base
S/D second-order output formula with cubic full-parameter remainder.
Use: the fixed-known-reference alternative in the source is fully
instantiated, including the true actual measured last trial error.
Article: main_krylov, thm:local(a), literal fixed known-CG implementation.
Proof: its genuine observed rule is calibrated and has constant smooth
trial charts at every finite input. Specialize the shared general native
formula; all moving frames, metric, incoming/replay fields and true
penultimate normalization are already derived by that theorem. -/
theorem fixedCGTrial_native_moving_output_cubic (directions : Bool)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1)
    (A : X → ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hA : ∀ j,ContDiffAt ℝ 1 (fun z => A z j) 0)
    (hsym : ∀ z j,(A z j).IsSymm) (hA0 : ∀ j,A 0 j=base)
    (hpos : ∀ᶠ z in 𝓝 (0 : X),(A z 0).PosDef) :
    let trial := fixedCGTrial base g
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
        =O[𝓝 0] (fun z => ‖z‖^3) :=
  calibrated_native_moving_source_output_cubic directions (fixedCGTrial base g) base hb g hc
    (fixedCGTrial_calibrated base g (n+1)) (fun _ k _ => (fixedCGTrial_contDiff base g k).contDiffAt)
    A hA hsym hA0 hpos

end
end krylov.OneGradient
