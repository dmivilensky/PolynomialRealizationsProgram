import krylov.OneGradient.InformedSourceOutput
import krylov.OneGradient.InformedCanonicalCurvature
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a,b), actual informed pivot-resolved output.
Use: the genuine native S output has its complete original correlated
second-order coefficient in real prior, increments and output defect.
Source: actual source output formula, derived informed pivot remainder
and the real first-order output increment times quadratic error calculus.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Finset Filter Topology Asymptotics krylov.Methods krylov.Reference krylov.Secant
  krylov.Stability krylov.Correction krylov.Envelope
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The genuine informed S semantic output has the fully computed
correlated prior/increment second-order coefficient with a cubic remainder.
Only primitive C-one physical operators are assumed; all virtual fields,
incoming terms, true trial branches and their remainders are derived.
Use: the complete true native output is ready for original known-base
sharp upper bounds and actual physical attaining source scenarios.
Article: main_krylov, thm:local(a,b), actual informed second-order output.
Proof: the actual output formula retains epsilon. Its proved real
curvature remainder is quadratic; the actual output increment is C-one
and zero at reference, hence first order. Their product is cubic.
Substitute the real prior-plus-increment diagonal in the actual formula. -/
theorem informed_step_pivot_output_cubic
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1)
    (A : X → ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hA : ∀ j,ContDiffAt ℝ 1 (fun z => A z j) 0)
    (hsym : ∀ z j,(A z j).IsSymm) (hA0 : ∀ j,A 0 j=base) :
    let trial := informedTrial (cgOperator base)
    let m := xrfcMethod fullMemory trial
    let op := fun z j => cgOperator (A z j)
    let E := fun z => canonicalIncrement base (A z)
    let h := canonicalCGUnitStep base g n
    let q := fun z => inner ℝ h (cgOperator (relativeOperator base (A z 0-base)+∑ l∈range n,E z l) h)
    (fun z => cgOperator (metricRoot base)⁻¹
      (m.outputGradient (op z (n+1)) (oneGradientRun m (op z) g (n+1)))+
        ‖cgCanonicalError base g n‖ •
          (staircaseOperator base g (E z) (E z n) (n+1) (freshDefect base g (E z) (n+1))+
            q z • cgOperator (E z n) h)) =O[𝓝 0] (fun z => ‖z‖^3) := by
  let trial := informedTrial (cgOperator base)
  let op := fun z j => cgOperator (A z j)
  let E := fun z => canonicalIncrement base (A z)
  let h := canonicalCGUnitStep base g n
  let q := fun z => inner ℝ h (cgOperator (relativeOperator base (A z 0-base)+∑ l∈range n,E z l) h)
  let eps := fun z => xrfcNativeTrialError false trial (op z) g n
  let v := fun z => cgOperator (E z n) h
  let sigma := ‖cgCanonicalError base g n‖
  have hr : (fun z => eps z+q z) =O[𝓝 0] (fun z => ‖z‖^2) :=
    informed_native_step_pivot_remainder base hb g hc A hA hA0
  have hv : ContDiffAt ℝ 1 v 0 := by
    have hM : ContDiffAt ℝ 1 (fun z => relativeOperator base (A z (n+1)-A z n)) 0 :=
      (contDiffAt_const.mul ((hA (n+1)).sub (hA n))).mul contDiffAt_const
    exact (matrixOperator_contDiffAt _ 0 hM).clm_apply contDiffAt_const
  have hv0 : v 0=0 := by
    simp only [v,E,canonicalIncrement,hA0,sub_self,relativeOperator,Matrix.mul_zero,Matrix.zero_mul,cgOperator,map_zero,_root_.zero_apply]
  have hvb : v =O[𝓝 0] (fun z => ‖z‖) := by
    simpa only [hv0,sub_zero] using (hv.differentiableAt (by norm_num)).isBigO_sub.norm_right
  have hprod : (fun z => sigma • ((eps z+q z) • v z)) =O[𝓝 0] (fun z => ‖z‖^3) := by
    exact ((hr.smul hvb).congr_right (fun z => by simp only [smul_eq_mul];ring)).const_smul_left sigma
  have hout := informed_source_output_cubic false base hb g hc A hA hsym hA0
  apply (hout.add hprod).congr_left
  intro z
  let out := cgOperator (metricRoot base)⁻¹ ((xrfcMethod fullMemory trial).outputGradient
    (op z (n+1)) (oneGradientRun (xrfcMethod fullMemory trial) (op z) g (n+1)))
  let u := staircaseOperator base g (E z) (E z n) (n+1) (freshDefect base g (E z) (n+1))
  change out+sigma • (u-eps z • v z)+sigma • ((eps z+q z) • v z)=
    out+sigma • (u+q z • v z)
  simp only [add_smul,smul_sub,smul_add]
  abel

end
end krylov.OneGradient
