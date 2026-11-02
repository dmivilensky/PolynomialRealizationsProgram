import krylov.OneGradient.InformedDirectionDomain
import krylov.OneGradient.DirectionLaunchDictionary
import krylov.OneGradient.ReplayLaunchCubic
import krylov.OneGradient.InformedTerminalBounds
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), genuine native informed direction launch.
Use: the actual implemented direction-basis output has the true cubic
frozen-flag formula from only primitive C-one physical segment operators.
Source: actual replay columns/images and quadratic error, true reference
basis domain, exact native output dictionary and full replay launch bound.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Filter Topology Asymptotics krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped BigOperators Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ}

/-- The actual full native informed direction-basis semantic output has
the frozen-reference-flag formula in the actual physical increments and
actual incoming gradient, with a cubic remainder from primitive C-one
data. Every true replay, trial, trajectory and inverse-domain premise is
derived for the original implementation; no exact varying replay is assumed.
Use: closes the real full direction-output cubic assembly before the
explicit first-order incoming-gradient coefficient is substituted.
Article: main_krylov, thm:local(a), genuine direction-basis cubic launch.
Proof: genuine informed query calculus supplies the actual direction and
image matrices and their quadratic difference from true operator images.
The reference has a derived true full basis and zero incoming gradient.
Apply the real replay-model cubic launch theorem. The exact genuine native
output dictionary identifies this estimate with the implemented output. -/
theorem informed_direction_launch_cubic
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hc : referenceAtomCount base hb g=n) (hn : 0< n)
    (A : X → ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ k,ContDiffAt ℝ 1 (fun z => A z k) 0)
    (hsym : ∀ z k,(A z k).IsSymm) (hA0 : ∀ k,A 0 k=base) :
    let trial := informedTrial (cgOperator base)
    let m := xrfcDMethod fullMemory trial
    let op := fun z k => cgOperator (A z k)
    let G := fun z => oneGradientGradient m (op z) g n
    let R := cgOperator (metricRoot base)⁻¹
    let P := fun l => transportedFlag (metricRoot base*informedDirectionColumns base A g 0) l
    (fun z => R (m.outputGradient (op z n) (oneGradientRun m (op z) g n))+
      ∑ l∈Finset.range n,cgOperator (P l)ᵀ
        ((R*(op z (l+1)-op z l)*R) (cgOperator (P l) (R (G z)))))
      =O[𝓝 0] (fun z => ‖z‖^3) := by
  let trial := informedTrial (cgOperator base)
  let m := xrfcDMethod fullMemory trial
  let op := fun z k => cgOperator (A z k)
  let G := fun z => oneGradientGradient m (op z) g n
  let D := informedDirectionColumns base A g
  let Y := informedDirectionImages base A g
  let R := cgOperator (metricRoot base)⁻¹
  obtain ⟨hD,hY,hY0,herror⟩ := informed_direction_columns_data base hb g hc A hA hA0
  have hu := informed_direction_columns_nonsingular base hb g hc A hA0
  have hp := cgOperator_positive base hb
  have hpre : ∀ i<n,CG.gradient (cgOperator base) g i≠0 := fun i hi => cg_nonstagnation base hb g i (by rw [hc];exact hi)
  have hop : ∀ k,ContDiffAt ℝ 1 (fun z => op z k) 0 := fun k => matrixOperator_contDiffAt _ 0 (hA k)
  have hop0 : op 0=fun _ => cgOperator base := funext (fun k => congrArg cgOperator (hA0 k))
  have hG : ContDiffAt ℝ 1 G 0 :=
    (quadraticXRFCD_prefix_contDiffAt trial op (fun _ => g) 0 hop contDiffAt_const (cgOperator base) hop0
      hp.1 hp.2 n hpre (fun _ _ => (informed_trial_positive (cgOperator base) _).ne') (fun i hi => by
        rw [hop0]
        exact informed_trial_reference_contDiff true base hb base hb g n hpre i hi 1)).1 n le_rfl
  have hG0 : G 0=0 := by
    change oneGradientGradient m (op 0) g n=0
    rw [hop0]
    exact informed_terminal_gradient_zero true base hb g hc hn
  have h := replay_launch_cubic_remainder base hb D Y hD hY hu A hA hsym hA0 hY0 herror G hG hG0
  have hunit : ∀ᶠ z in 𝓝 (0 : X),IsUnit (D z).det :=
    (hD.continuousAt.eventually (Units.isOpen.mem_nhds ((Matrix.isUnit_iff_isUnit_det _).mpr hu))).mono
      (fun _ hz => (Matrix.isUnit_iff_isUnit_det _).mp hz)
  apply h.congr' ?_ EventuallyEq.rfl
  filter_upwards [hunit] with z hz
  have he := xrfcD_semantic_replay_dictionary trial (A z) g hz
  change R (G z-op z n (cgOperator (replayLaunchModel (D z) (Y z))⁻¹ (G z)))+_=
    R (m.outputGradient (op z n) (oneGradientRun m (op z) g n))+_
  rw [he]
  rfl

end
end krylov.OneGradient
