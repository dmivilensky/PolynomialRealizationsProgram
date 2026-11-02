import krylov.OneGradient.LaunchVanishingRemainder
import krylov.OneGradient.InformedTerminalBounds
import krylov.OneGradient.XRFCLaunchDictionary
import krylov.Stability.ContDiffSpectralMatrix
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), genuine informed step-basis cubic launch.
Use: instantiate the actual full-gradient cubic launch formula on the
implemented informed one-gradient executor, with every native chart derived.
Source: primitive physical operators, true informed native regularity and
evaluated-gradient zero, actual full columns and the real solve dictionary.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Methods krylov.Reference krylov.Stability krylov.Secant krylov.Correction
open Matrix Filter Topology Asymptotics
open scoped BigOperators Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ}

/-- The actual complete chronological physical step columns of the
genuine informed full-memory one-gradient executor.
Use: the known-base expansion retains the true original observations.
Article: main_krylov, thm:local(a), genuine informed step basis. -/
def informedStepColumns (base : Matrix (Fin n) (Fin n) ℝ)
    (A : X → ℕ → Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (z : X) :
    Matrix (Fin n) (Fin n) ℝ := fullBasisMatrix (fun i : Fin n =>
      oneGradientStep (xrfcMethod fullMemory (informedTrial (cgOperator base))) (fun k => cgOperator (A z k)) g i.val)

/-- The actual implemented informed step-basis output has the genuine
frozen-reference-flag formula with the actual increments and actual last
evaluated gradient, with a cubic remainder in the full parameter norm.
Only primitive C-one physical operators are assumed: all actual trial
charts, trajectory regularity, column/inverse domains and incoming zero
are derived for the real original executor.
Use: native known-base second-order output before evaluating the explicit
first-order incoming-gradient coefficient; no output expansion is assumed.
Article: main_krylov, thm:local(a), genuine step-basis cubic launch.
Proof: the proved primitive informed charts give genuine C-one executed
steps and gradients. Actual full reference atoms give the genuine column
inverse domain. Exact informed calibration makes the true evaluated
gradient zero. Apply the actual cubic launch theorem and identify the
literal native output by its genuine chronological observed-model solve. -/
theorem informed_step_launch_cubic
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hc : referenceAtomCount base hb g=n) (hn : 0< n)
    (A : X → ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ k,ContDiffAt ℝ 1 (fun z => A z k) 0)
    (hsym : ∀ z k,(A z k).IsSymm) (hA0 : ∀ k,A 0 k=base) :
    let trial := informedTrial (cgOperator base)
    let m := xrfcMethod fullMemory trial
    let op := fun z k => cgOperator (A z k)
    let G := fun z => oneGradientGradient m (op z) g n
    let R := cgOperator (metricRoot base)⁻¹
    let P := fun l => transportedFlag (metricRoot base*informedStepColumns base A g 0) l
    (fun z => R (m.outputGradient (op z n) (oneGradientRun m (op z) g n))+
      ∑ l∈Finset.range n,cgOperator (P l)ᵀ
        ((R*(op z (l+1)-op z l)*R) (cgOperator (P l) (R (G z)))))
      =O[𝓝 0] (fun z => ‖z‖^3) := by
  let trial := informedTrial (cgOperator base)
  let m := xrfcMethod fullMemory trial
  let op := fun z k => cgOperator (A z k)
  let G := fun z => oneGradientGradient m (op z) g n
  let S := informedStepColumns base A g
  let R := cgOperator (metricRoot base)⁻¹
  let P := fun l => transportedFlag (metricRoot base*S 0) l
  have hp := cgOperator_positive base hb
  have hpre : ∀ i< n,CG.gradient (cgOperator base) g i≠0 :=
    fun i hi => cg_nonstagnation base hb g i (by rw [hc];exact hi)
  have hop : ∀ i,ContDiffAt ℝ 1 (fun z => op z i) 0 := fun i => matrixOperator_contDiffAt _ 0 (hA i)
  have hop0 : op 0=fun _ => cgOperator base := funext (fun k => congrArg cgOperator (hA0 k))
  have ht : ∀ i< n,trial (oneGradientRun m (fun _ => cgOperator base) g i)≠0 :=
    fun _ _ => (informed_trial_positive (cgOperator base) _).ne'
  have hreg := quadraticXRFC_prefix_contDiffAt trial op (fun _ => g) 0 hop contDiffAt_const
    (cgOperator base) hop0 hp.1 hp.2 n hpre ht (fun i hi => by
      rw [hop0]
      exact informed_trial_reference_contDiff false base hb base hb g n hpre i hi 1)
  have hS : ContDiffAt ℝ 1 S 0 := by
    apply contDiff_spectral_matrix
    intro i j
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).contDiff.contDiffAt.comp 0 (hreg.2 j.val j.isLt)
  have hS0 : S 0=xrfcPhysicalColumns trial base g := by
    change fullBasisMatrix (fun i : Fin n => oneGradientStep m (op 0) g i.val)=_
    rw [hop0]
    rfl
  have hu : IsUnit (S 0).det := by rw [hS0];exact (xrfc_columns_nonsingular trial base hb g hc ht).1
  have hG : ContDiffAt ℝ 1 G 0 := hreg.1 n le_rfl
  have hG0 : G 0=0 := by
    change oneGradientGradient m (op 0) g n=0
    rw [hop0]
    exact informed_terminal_gradient_zero false base hb g hc hn
  have h := launch_semantic_c1_vanishing_gradient_remainder base hb S hS hu A hA hsym hA0 G hG hG0
  have hunit : ∀ᶠ z in 𝓝 (0 : X),IsUnit (S z).det :=
    (hS.continuousAt.eventually (Units.isOpen.mem_nhds ((Matrix.isUnit_iff_isUnit_det _).mpr hu))).mono
      (fun _ hz => (Matrix.isUnit_iff_isUnit_det _).mp hz)
  apply h.congr' ?_ EventuallyEq.rfl
  filter_upwards [hunit] with z hz
  have he := xrfc_semantic_launch_dictionary trial (A z) g hz
  change R (launchSemanticGradient (S z) (A z) (G z))+_=R (m.outputGradient (op z n) (oneGradientRun m (op z) g n))+_
  rw [he]
  rfl

end
end krylov.OneGradient
