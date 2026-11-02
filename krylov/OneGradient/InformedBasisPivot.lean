import krylov.OneGradient.InformedDirectionCurvature
import krylov.OneGradient.InformedPivotOutput
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a,b), both actual informed native pivots.
Use: the real history-only informed S and D policies have the same fully
computed correlated physical coefficient with a genuine cubic remainder.
Source: actual native curvature jets, canonical CG normalization and the
shared genuine both-basis semantic output expansion.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Finset Filter Topology Asymptotics krylov.Methods krylov.Reference krylov.Secant
  krylov.Stability krylov.Correction krylov.Envelope
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The true implemented informed S/D last-pivot error has the original
prior-plus-increments coefficient with a quadratic primitive-parameter
remainder. The direction, quotient branch and every actual smoothness
domain are derived from the observed implementation.
Use: supplies the genuine unmeasured-pivot coefficient for the original
known-base upper estimates and physical attaining source families.
Article: main_krylov, thm:local(a), actual informed epsilon expansion.
Proof: use the proved genuine native physical curvature remainder. Its
actual frozen CG quotient is exactly its unit-CG canonical diagonal;
the true physical prior and all observed increments telescope exactly. -/
theorem informed_native_basis_pivot_remainder
    (directions : Bool)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1)
    (A : X → ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hA : ∀ j,ContDiffAt ℝ 1 (fun z => A z j) 0) (hA0 : ∀ j,A 0 j=base) :
    let op := fun z j => cgOperator (A z j)
    let h := canonicalCGUnitStep base g n
    (fun z => xrfcNativeTrialError directions (informedTrial (cgOperator base)) (op z) g n+
      inner ℝ h (cgOperator (relativeOperator base (A z 0-base)+
        ∑ l∈range n,canonicalIncrement base (A z) l) h)) =O[𝓝 0] (fun z => ‖z‖^2) := by
  let op := fun z j => cgOperator (A z j)
  have hop : ∀ j,ContDiffAt ℝ 1 (fun z => op z j) 0 := fun j => matrixOperator_contDiffAt _ 0 (hA j)
  have hop0 : op 0=fun _ => cgOperator base := funext (fun j => congrArg cgOperator (hA0 j))
  have hk : n<referenceAtomCount base hb g := by omega
  have hr : (fun z => xrfcNativeTrialError directions (informedTrial (cgOperator base)) (op z) g n+
      inner ℝ (CG.direction (cgOperator base) g n) ((op z n-cgOperator base) (CG.direction (cgOperator base) g n))/
        inner ℝ (CG.direction (cgOperator base) g n) (cgOperator base (CG.direction (cgOperator base) g n)))
        =O[𝓝 0] (fun z => ‖z‖^2) := by
    cases directions with
    | false =>
      exact informed_native_step_curvature_remainder base hb g (n+1)
        (fun i hi => cg_nonstagnation base hb g i (by omega)) op hop hop0 n (by omega)
    | true =>
      exact informed_native_direction_curvature_remainder base hb g (n+1)
        (fun i hi => cg_nonstagnation base hb g i (by omega)) op hop hop0 n (by omega)
  apply hr.congr_left
  intro z
  have he : op z n-cgOperator base=cgOperator (A z n-base) := by simp only [op,cgOperator,map_sub]
  rw [he,canonicalCG_curvature_quotient base hb g n hk,
    ← canonical_prior_increment_sum base (A z) n]
  simp only [op,relativeOperator,cgOperator,map_mul,map_sub]


/-- The genuine informed S/D semantic output has the fully computed
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
theorem informed_basis_pivot_output_cubic
    (directions : Bool)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1)
    (A : X → ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hA : ∀ j,ContDiffAt ℝ 1 (fun z => A z j) 0)
    (hsym : ∀ z j,(A z j).IsSymm) (hA0 : ∀ j,A 0 j=base) :
    let trial := informedTrial (cgOperator base)
    let m := xrfcBasisMethod directions trial
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
  let eps := fun z => xrfcNativeTrialError directions trial (op z) g n
  let v := fun z => cgOperator (E z n) h
  let sigma := ‖cgCanonicalError base g n‖
  have hr : (fun z => eps z+q z) =O[𝓝 0] (fun z => ‖z‖^2) :=
    informed_native_basis_pivot_remainder directions base hb g hc A hA hA0
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
  have hout := informed_source_output_cubic directions base hb g hc A hA hsym hA0
  apply (hout.add hprod).congr_left
  intro z
  let out := cgOperator (metricRoot base)⁻¹ ((xrfcBasisMethod directions trial).outputGradient
    (op z (n+1)) (oneGradientRun (xrfcBasisMethod directions trial) (op z) g (n+1)))
  let u := staircaseOperator base g (E z) (E z n) (n+1) (freshDefect base g (E z) (n+1))
  change out+sigma • (u-eps z • v z)+sigma • ((eps z+q z) • v z)=
    out+sigma • (u+q z • v z)
  simp only [add_smul,smul_sub,smul_add]
  abel

end
end krylov.OneGradient
