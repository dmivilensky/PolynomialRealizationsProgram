import krylov.OneGradient.InformedIncomingVector
import krylov.OneGradient.InformedStepLaunch
import krylov.OneGradient.InformedDirectionLaunch
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), actual informed native second-order output.
Use: combine the genuine full incoming-gradient derivation with both
actual native cubic launch formulas, from only primitive C-one data.
Source: true observed/replay basis dictionaries, actual incoming drift
and relative trial error, and genuine vanishing operator action orders.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Filter Topology Asymptotics krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The genuine reference native full basis used in the actual S or D
output. Every column comes from the implemented informed executor.
Use: final second-order formulas keep the correct native physical basis.
Article: main_krylov, thm:local(a), actual native full reference basis. -/
def informedNativeReferenceColumns (directions : Bool) (base : Matrix (Fin n) (Fin n) ℝ)
    (A : X → ℕ → Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  if directions then informedDirectionColumns base A g 0 else informedStepColumns base A g 0

/-- The actual-increment compressed operator with genuine frozen native
reference flags. The output increment is included in its original last slot.
Use: the native output formula retains full current physical increments,
without replacing them by derivatives or a supplied second-order model.
Article: main_krylov, thm:local(a), actual leading operator L. -/
def informedNativeLaunchOperator (directions : Bool) (base : Matrix (Fin n) (Fin n) ℝ)
    (A : X → ℕ → Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (z : X) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  let R := cgOperator (metricRoot base)⁻¹
  let P := fun l => transportedFlag (metricRoot base*informedNativeReferenceColumns directions base A g) l
  ∑ l∈Finset.range n,cgOperator (P l)ᵀ*(R*(cgOperator (A z (l+1))-cgOperator (A z l))*R)*cgOperator (P l)

/-- The actual full-cycle informed S/D semantic output has its explicit
second-order incoming-drift/relative-trial-error coefficient with a genuine
cubic remainder in the full primitive perturbation parameter. The actual
increments and true native trial errors are retained throughout.
Use: the known-base expansion now concerns the real native output with
its full incoming vector computed, rather than an assumed gradient jet.
Article: main_krylov, thm:local(a), genuine explicit native output expansion.
Proof: genuine native reference flags and primitive operators give a true
C-one compressed operator vanishing at the quadratic reference, hence
first order. The proved actual incoming-vector remainder is quadratic,
so its action contributes only cubic order. Subtract that real remainder
from the actual native cubic launch theorem and distribute the true
linear operator over the explicit incoming leading vector. -/
theorem informed_native_output_cubic (directions : Bool)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1)
    (A : X → ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hA : ∀ j,ContDiffAt ℝ 1 (fun z => A z j) 0)
    (hsym : ∀ z j,(A z j).IsSymm) (hA0 : ∀ j,A 0 j=base) :
    let trial := informedTrial (cgOperator base)
    let m := xrfcBasisMethod directions trial
    let op := fun z k => cgOperator (A z k)
    let R := cgOperator (metricRoot base)⁻¹
    let L := informedNativeLaunchOperator directions base A g
    (fun z => R (m.outputGradient (op z (n+1)) (oneGradientRun m (op z) g (n+1)))+
      ‖canonicalCGStep base g n‖ • L z (informedIncomingDrift base g (op z)-
        xrfcNativeTrialError directions trial (op z) g n • canonicalCGUnitStep base g n))
        =O[𝓝 0] (fun z => ‖z‖^3) := by
  let trial := informedTrial (cgOperator base)
  let m := xrfcBasisMethod directions trial
  let op := fun z k => cgOperator (A z k)
  let R := cgOperator (metricRoot base)⁻¹
  let L := informedNativeLaunchOperator directions base A g
  let G := fun z => R (oneGradientGradient m (op z) g (n+1))
  let out := fun z => R (m.outputGradient (op z (n+1)) (oneGradientRun m (op z) g (n+1)))
  let sigma := ‖canonicalCGStep base g n‖
  let v := fun z => informedIncomingDrift base g (op z)-
    xrfcNativeTrialError directions trial (op z) g n • canonicalCGUnitStep base g n
  have hop : ∀ j,ContDiffAt ℝ 1 (fun z => op z j) 0 := fun j => matrixOperator_contDiffAt _ 0 (hA j)
  have hop0 : op 0=fun _ => cgOperator base := funext (fun j => congrArg cgOperator (hA0 j))
  have hopSym : ∀ z j,(op z j).toLinearMap.IsSymmetric := fun z j =>
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_iff_isSymm.mpr (hsym z j))
  have hLreg : ContDiffAt ℝ 1 L 0 := by
    apply ContDiffAt.sum
    intro j _
    exact (contDiffAt_const.mul
      ((contDiffAt_const.mul ((hop (j+1)).sub (hop j))).mul contDiffAt_const)).mul contDiffAt_const
  have hL0 : L 0=0 := by
    simp only [L,informedNativeLaunchOperator,hA0,sub_self,mul_zero,zero_mul,Finset.sum_const_zero]
  have hL : L =O[𝓝 0] (fun z => ‖z‖) := by
    simpa only [hL0,sub_zero] using (hLreg.differentiableAt (by norm_num)).isBigO_sub.norm_right
  have hin : (fun z => G z-sigma • v z) =O[𝓝 0] (fun z => ‖z‖^2) :=
    informed_native_incoming_vector directions base hb g hc op hop hop0 hopSym
  have hprod : (fun z => L z (G z-sigma • v z)) =O[𝓝 0] (fun z => ‖z‖^3) := by
    exact (clm_apply_bigO L (fun z => G z-sigma • v z) _ _ hL hin).congr_right (fun z => by ring)
  have hlaunch : (fun z => out z+L z (G z)) =O[𝓝 0] (fun z => ‖z‖^3) := by
    cases directions with
    | false =>
      have h := informed_step_launch_cubic base hb g hc (by omega) A hA hsym hA0
      simpa only [L,informedNativeLaunchOperator,informedNativeReferenceColumns,Bool.false_eq_true,ite_false,
        out,G,m,trial,R,op,xrfcBasisMethod,_root_.sum_apply,mul_apply_eq_comp] using h
    | true =>
      have h := informed_direction_launch_cubic base hb g hc (by omega) A hA hsym hA0
      simpa only [L,informedNativeLaunchOperator,informedNativeReferenceColumns,ite_true,
        out,G,m,trial,R,op,xrfcBasisMethod,_root_.sum_apply,mul_apply_eq_comp] using h
  apply (hlaunch.sub hprod).congr_left
  intro z
  rw [map_sub,map_smul]
  abel

end
end krylov.OneGradient
