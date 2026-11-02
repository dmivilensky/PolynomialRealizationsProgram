import krylov.OneGradient.ReplayLaunchModel
import krylov.OneGradient.LaunchVanishingRemainder
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), true full replay-output cubic stability.
Use: actual quadratic native image errors contribute only cubic order to
the genuine full output when its actual incoming gradient vanishes.
Source: real full inverse-model comparison, operator norm action calculus
and the actual primitive-C1 frozen-flag launch theorem.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Filter Topology Asymptotics krylov.Secant krylov.Reference krylov.Stability krylov.LinearAlgebra
open scoped Matrix.Norms.L2Operator BigOperators
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The true full replay-model output obeys the same genuine cubic
frozen-flag launch formula as the actual-image model, retaining its real
replayed images, actual increments and actual incoming gradient.
Use: quadratic native direction replay error is never silently set to zero.
Article: main_krylov, thm:local(a), genuine direction-output cubic comparison.
Proof: the actual inverse replay model differs quadratically from the
actual-image inverse model. The true incoming gradient is first order,
so their genuine output difference is cubic. The actual-image launch
has the proved primitive-C1 cubic remainder; add the two real estimates. -/
theorem replay_launch_cubic_remainder
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (S Y : X → Matrix (Fin n) (Fin n) ℝ)
    (hS : ContDiffAt ℝ 1 S 0) (hY : ContDiffAt ℝ 1 Y 0) (hu : IsUnit (S 0).det)
    (A : X → ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ k,ContDiffAt ℝ 1 (fun z => A z k) 0) (hsym : ∀ z k,(A z k).IsSymm)
    (hA0 : ∀ k,A 0 k=base) (hY0 : Y 0=pairImages (S 0) (A 0))
    (herror : (fun z => Y z-pairImages (S z) (A z)) =O[𝓝 0] (fun z => ‖z‖^2))
    (G : X → EuclideanSpace ℝ (Fin n)) (hG : ContDiffAt ℝ 1 G 0) (hG0 : G 0=0) :
    let R := cgOperator (metricRoot base)⁻¹
    let P := fun l => transportedFlag (metricRoot base*S 0) l
    (fun z => R (G z-cgOperator (A z n) (cgOperator (replayLaunchModel (S z) (Y z))⁻¹ (G z)))+
      ∑ l∈Finset.range n,cgOperator (P l)ᵀ
        ((R*(cgOperator (A z (l+1))-cgOperator (A z l))*R) (cgOperator (P l) (R (G z)))))
        =O[𝓝 0] (fun z => ‖z‖^3) := by
  let R := cgOperator (metricRoot base)⁻¹
  let J := fun z => replayLaunchModel (S z) (Y z)
  let K := fun z => launchObservedModel (S z) (A z)
  have hinv := replay_launch_inverse_quadratic base hb S Y hS hY hu A hA hA0 hY0 herror
  let L := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).toAlgEquiv.toLinearMap.toContinuousLinearMap
  have hop : (fun z => cgOperator ((J z)⁻¹-(K z)⁻¹)) =O[𝓝 0] (fun z => ‖z‖^2) :=
    (L.isBigO_comp (fun z => (J z)⁻¹-(K z)⁻¹) (𝓝 0)).trans hinv
  have hg : G =O[𝓝 0] (fun z => ‖z‖) := by
    simpa only [hG0,sub_zero] using (hG.differentiableAt (by norm_num)).isBigO_sub.norm_right
  have hact : (fun z => cgOperator ((J z)⁻¹-(K z)⁻¹) (G z)) =O[𝓝 0] (fun z => ‖z‖^3) := by
    simpa only [← pow_succ] using operator_action_order _ _ _ _ hop hg
  have houter : (fun z => R*cgOperator (A z n)) =O[𝓝 0] (fun _ => (1 : ℝ)) :=
    ((contDiffAt_const.mul (matrixOperator_contDiffAt _ 0 (hA n))).continuousAt.tendsto).isBigO_one ℝ
  have hfull : (fun z => -((R*cgOperator (A z n)) (cgOperator ((J z)⁻¹-(K z)⁻¹) (G z))))
      =O[𝓝 0] (fun z => ‖z‖^3) := by
    simpa only [one_mul] using (operator_action_order _ _ _ _ houter hact).neg_left
  have hdiff : (fun z => R (G z-cgOperator (A z n) (cgOperator (J z)⁻¹ (G z)))-
      R (launchSemanticGradient (S z) (A z) (G z))) =O[𝓝 0] (fun z => ‖z‖^3) := by
    apply hfull.congr_left
    intro z
    simp only [launchSemanticGradient,K,map_sub,cgOperator,_root_.sub_apply,mul_apply_eq_comp]
    abel
  have hlaunch := launch_semantic_c1_vanishing_gradient_remainder base hb S hS hu A hA hsym hA0 G hG hG0
  apply (hdiff.add hlaunch).congr_left
  intro z
  dsimp only
  abel

end
end krylov.OneGradient
