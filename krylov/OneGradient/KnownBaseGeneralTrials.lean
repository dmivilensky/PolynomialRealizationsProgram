import krylov.OneGradient.CalibratedMovingOutput
import krylov.OneGradient.CalibratedTrialOrder
import krylov.OneGradient.XRFCBidiagonal
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), original general reference-error premise.
Use: the printed O(omega) reference trial errors imply the actual known
calibration, and the real S/D output has the original own-A0 cubic formula.
Source: the original measured reference error, genuine active CG positivity,
and the proved complete native calibrated output and moving-frame calculus.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Filter Topology Asymptotics krylov.Methods krylov.Reference krylov.Secant
  krylov.Stability krylov.Correction krylov.Envelope
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X]

/-- The original first-order reference trial-error hypothesis forces
true exact calibration at the known limiting quadratic reference.
Use: the general source theorem needs the printed error premise, rather
than an additional calibration or prescribed reference trajectory premise.
Article: main_krylov, thm:local(a), original small-error calibration bridge.
Proof: a genuine full-neighborhood big-O bound vanishes at zero. The
original relative error is one minus the actual trial over the true CG
length; active positivity permits cancellation of that actual denominator. -/
theorem reference_trial_error_order_calibrates
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (hpre : ∀ i<N,CG.gradient (cgOperator base) g i≠0)
    (B : X → Matrix (Fin n) (Fin n) ℝ) (hB0 : B 0=base)
    (herror : ∀ k<N,(fun z => xrfcTrialError trial (B z) g k) =O[𝓝 0] (fun z => ‖z‖)) :
    CalibratedTrial trial (cgOperator base) g N := by
  have hp := cgOperator_positive base hb
  intro k hk
  have hz : xrfcTrialError trial (B 0) g k=0 := (herror k hk).eq_zero_imp.self_of_nhds (norm_zero : ‖(0 : X)‖=0)
  rw [hB0] at hz
  have ha := (CG.invariant_line_pos (cgOperator base) hp.2 g k
    (CG.invariant (cgOperator base) hp.1 hp.2 g k (fun i hi => hpre i (hi.trans hk))) (hpre k hk)).2.1.ne'
  have hquot : trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g k)/
      CG.length (cgOperator base) g k=1 := by
    change 1-(_/_)=0 at hz
    linarith
  exact (div_eq_one_iff_eq ha).mp hquot

variable [NormedSpace ℝ X]

/-- Under the original first-order reference trial-error premise, the
actual full-memory S/D output has exactly the printed second-order
fresh-defect/staircase formula in its own true A0 metric and CG frame.
Its final epsilon is the actual measured native error; its normalization
is the source's own true penultimate CG-error norm. The joint remainder
is cubic in the full primitive perturbation parameter.
Use: closes the original general known-base assertion with the source's
error hypothesis, not an assumed incoming/output jet or a special policy.
Article: main_krylov, thm:local(a), complete original general native formula.
Proof: the printed reference errors force actual known-reference
calibration. Primitive observed trial charts and operators then derive
all native data, domains and replay orders. Specialize the complete
calibrated own-reference output theorem, which proves the actual incoming
coefficient and moving metric/frame/normalization transfer. -/
theorem knownBase_general_trial_output_cubic (directions : Bool)
    (trial : History (EuclideanSpace ℝ (Fin (n+1))) → ℝ)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1)
    (A : X → ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hA : ∀ j,ContDiffAt ℝ 1 (fun z => A z j) 0)
    (hsym : ∀ z j,(A z j).IsSymm) (hA0 : ∀ j,A 0 j=base)
    (hpos : ∀ᶠ z in 𝓝 (0 : X),(A z 0).PosDef)
    (hT : ∀ (directions : Bool) (k : ℕ),k<n+1 → ContDiffAt ℝ 1 (trialCoordinate trial k)
      (oneGradientData (xrfcBasisMethod directions trial) (fun _ => cgOperator base) g k))
    (herror : ∀ k<n+1,(fun z => xrfcTrialError trial (A z 0) g k) =O[𝓝 0] (fun z => ‖z‖)) :
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
  have hcal := reference_trial_error_order_calibrates trial base hb g (n+1)
    (fun i hi => cg_nonstagnation base hb g i (by omega)) (fun z => A z 0) (hA0 0) herror
  exact calibrated_native_moving_source_output_cubic directions trial base hb g hc hcal hT A hA hsym hA0 hpos

end
end krylov.OneGradient
