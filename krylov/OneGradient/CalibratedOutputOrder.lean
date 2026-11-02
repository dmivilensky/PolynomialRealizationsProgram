import krylov.OneGradient.CalibratedNativeOutput
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), genuine native output order.
Use: derive quadratic order of the actual implemented physical S/D output
before changing its metric to the original source's moving actual base.
Source: real native cubic launch, true incoming-gradient first-order
bound and actual vanishing compressed operator calculus.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Filter Topology Asymptotics krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual complete native calibrated S/D physical semantic output is
quadratic in the full primitive parameter, with every trajectory, replay,
calibration and inverse-domain premise derived from primitive C-one data.
Use: its genuine moving metric variation contributes only cubic order.
Article: main_krylov, thm:local(a), actual physical output is O(norm(z)^2).
Proof: the actual native cubic launch contains the true incoming gradient,
which is first order, multiplied by the actual compressed increment operator,
also first order. Their genuine product is quadratic; the cubic remainder
is smaller. Cancel the fixed positive root to recover the physical output. -/
theorem calibrated_native_output_quadratic (directions : Bool)
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
    let op := fun z j => cgOperator (A z j)
    (fun z => m.outputGradient (op z (n+1)) (oneGradientRun m (op z) g (n+1)))
      =O[𝓝 0] (fun z => ‖z‖^2) := by
  let m := xrfcBasisMethod directions trial
  let op := fun z j => cgOperator (A z j)
  let R := cgOperator (metricRoot base)⁻¹
  let L := calibratedNativeLaunchOperator directions trial base A g
  let G := fun z => R (oneGradientGradient m (op z) g (n+1))
  let out := fun z => m.outputGradient (op z (n+1)) (oneGradientRun m (op z) g (n+1))
  have hop : ∀ j,ContDiffAt ℝ 1 (fun z => op z j) 0 := fun j => matrixOperator_contDiffAt _ 0 (hA j)
  have hop0 : op 0=fun _ => cgOperator base := funext (fun j => congrArg cgOperator (hA0 j))
  have hp := cgOperator_positive base hb
  have hpre : ∀ i<n+1,CG.gradient (cgOperator base) g i≠0 := fun i hi => cg_nonstagnation base hb g i (by omega)
  have hgrad := (calibrated_native_prefix_contDiff directions trial base hb g (n+1) hpre hcal hT op hop hop0).1 (n+1) le_rfl
  change ContDiffAt ℝ 1 (fun z => oneGradientGradient m (op z) g (n+1)) 0 at hgrad
  have hzero : oneGradientGradient m (op 0) g (n+1)=0 := by
    rw [hop0]
    exact calibrated_native_terminal_zero directions trial base hb g hc hcal
  have hG : G =O[𝓝 0] (fun z => ‖z‖) := by
    have hgo : (fun z => oneGradientGradient m (op z) g (n+1)) =O[𝓝 0] (fun z => ‖z‖) := by
      simpa only [hzero,sub_zero] using (hgrad.differentiableAt (by norm_num)).isBigO_sub.norm_right
    exact (R.isBigO_comp _ (𝓝 0)).trans hgo
  have hLreg : ContDiffAt ℝ 1 L 0 := by
    apply ContDiffAt.sum
    intro j _
    exact (contDiffAt_const.mul
      ((contDiffAt_const.mul ((hop (j+1)).sub (hop j))).mul contDiffAt_const)).mul contDiffAt_const
  have hL0 : L 0=0 := by
    simp only [L,calibratedNativeLaunchOperator,hA0,sub_self,mul_zero,zero_mul,Finset.sum_const_zero]
  have hL : L =O[𝓝 0] (fun z => ‖z‖) := by
    simpa only [hL0,sub_zero] using (hLreg.differentiableAt (by norm_num)).isBigO_sub.norm_right
  have hprod : (fun z => L z (G z)) =O[𝓝 0] (fun z => ‖z‖^2) := by
    simpa only [← sq] using clm_apply_bigO L G _ _ hL hG
  have hlaunch : (fun z => R (out z)+L z (G z)) =O[𝓝 0] (fun z => ‖z‖^3) := by
    cases directions with
    | false =>
      have h := calibrated_step_launch_cubic trial base hb g hc hcal hT A hA hsym hA0
      simpa only [L,calibratedNativeLaunchOperator,calibratedNativeReferenceColumns,Bool.false_eq_true,ite_false,
        out,G,m,R,op,xrfcBasisMethod,_root_.sum_apply,mul_apply_eq_comp] using h
    | true =>
      have h := calibrated_direction_launch_cubic trial base hb g hc hcal hT A hA hsym hA0
      simpa only [L,calibratedNativeLaunchOperator,calibratedNativeReferenceColumns,ite_true,
        out,G,m,R,op,xrfcBasisMethod,_root_.sum_apply,mul_apply_eq_comp] using h
  have hcan : (fun z => R (out z)) =O[𝓝 0] (fun z => ‖z‖^2) := by
    exact ((hlaunch.trans (isLittleO_norm_pow_norm_pow (by norm_num : 2<3)).isBigO).sub hprod).congr_left
      (fun z => by abel)
  have hphysical := ((cgOperator (metricRoot base)).isBigO_comp _ (𝓝 0)).trans hcan
  apply hphysical.congr_left
  intro z
  change cgOperator (metricRoot base) (cgOperator (metricRoot base)⁻¹ (out z))=out z
  simp only [cgOperator,← mul_apply_eq_comp,← map_mul,Matrix.mul_nonsing_inv _ (metricRoot_det_unit base hb),map_one,one_apply_eq_self]

end
end krylov.OneGradient
