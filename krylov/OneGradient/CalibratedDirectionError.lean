import krylov.Stability.DirectionCoefficientRegularity
import krylov.Methods.DirectionWeights
import krylov.Stability.C1VanishingProduct
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), genuine calibrated direction-image order.
Use: derive the actual native direction replay's quadratic image error
from primitive C-one data and exact quadratic-reference trial calibration.
Source: exact native image recursion, genuine primitive query/solve
regularity and the two true first-order vanishing factors in every term.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Methods krylov.Reference krylov.Stability
open Filter Topology Asymptotics
open scoped BigOperators
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The true native direction-basis replay has quadratic image error in
the full perturbation parameter whenever its genuine quadratic-reference
trials are exact, from only primitive C-one operator and trial charts.
Use: gives the original known-base O(omega²) direction-image term without
assuming a replay error estimate, a trajectory expansion or C-two data.
Article: main_krylov, thm:local(a), direction-basis cubic contribution.
Proof: actual reference virtual coefficients vanish by exact calibration.
Their genuine C-one charts give first-order coefficients. The genuine
drift/image brackets also vanish at the actual reference and have C-one
charts, hence first order. Each term of the exact native image recursion
therefore has quadratic order; the actual inverse trial is bounded.
All old image zeros and every inverse/solve domain are derived from the
genuine quadratic executor, independently of the perturbation path. -/
theorem calibrated_direction_image_quadratic
    (trial : History E → ℝ) (A : X → ℕ → E →L[ℝ] E)
    (hA : ∀ i,ContDiffAt ℝ 1 (fun z => A z i) 0)
    (Q : E →L[ℝ] E) (hA0 : A 0=fun _ => Q) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (N : ℕ)
    (hpre : ∀ i< N,CG.gradient Q g i≠0)
    (ht : ∀ i< N,trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => Q) g i)≠0)
    (hcal : ∀ i< N,trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => Q) g i)=CG.length Q g i)
    (hT : ∀ k< N,ContDiffAt ℝ 1 (trialCoordinate trial k)
      (oneGradientData (xrfcDMethod fullMemory trial) (fun _ => Q) g k))
    (j : ℕ) (hj : j< N) :
    (fun z => xrfcDImageError trial (A z) g j) =O[𝓝 0] (fun z => ‖z‖^2) := by
  let m := xrfcDMethod fullMemory trial
  have hcharts : ∀ k< N,ContDiffAt ℝ 1 (trialCoordinate trial k) (oneGradientData m (A 0) g k) := by
    rw [hA0]
    exact hT
  have hreg := quadraticXRFCD_prefix_contDiffAt trial A (fun _ => g) 0 hA contDiffAt_const
    Q hA0 hQ hpos N hpre ht hcharts
  have hI (k : ℕ) (hk : k< N) : ContDiffAt ℝ 1 (fun z => xrfcDImageError trial (A z) g k) 0 :=
    (hreg.2.2.2 k hk).sub ((hA k).clm_apply (hreg.2.2.1 k hk))
  have hI0 (k : ℕ) (hk : k< N) : xrfcDImageError trial (A 0) g k=0 := by
    rw [hA0,xrfcDImageError,xrfcD_executed_image_reference trial Q hQ hpos g N hpre ht k hk,
      xrfcD_executed_direction_reference trial Q hQ hpos g N hpre ht k hk.le,sub_self]
  let tau := fun z => trial (oneGradientRun m (A z) g j)
  let w := fun z => xrfcDArrayCoefficients trial (A z) g j
  let F := fun z (i : Fin j) =>
    (A z j-A z (j-1-i.val)) (xrfcDExecutedDirection trial (A z) g (j-1-i.val))-
      xrfcDImageError trial (A z) g (j-1-i.val)
  have htau := actual_trial_contDiffAt trial m A (fun _ => g) 0 j contDiffAt_const
    (fun i hi => hreg.2.1 i (hi.trans hj)) (fun i hi => hreg.1 i (hi.trans hj.le)) (hcharts j hj)
  have htau0 : tau 0≠0 := by dsimp only [tau];rw [hA0];exact ht j hj
  have hw (i : Fin j) : ContDiffAt ℝ 1 (fun z => w z i) 0 :=
    quadraticXRFCD_coefficients_contDiffAt trial A (fun _ => g) 0 hA contDiffAt_const Q hA0 hQ hpos
      N hpre ht hcharts j hj.le i
  have hw0 (i : Fin j) : w 0 i=0 := by
    have hjp : 0< j := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
    dsimp only [w]
    rw [hA0,xrfcD_reference_coefficients_at trial Q hQ hpos g N hpre ht j hj.le hjp]
    have hcal0 := hcal (j-1) (by omega)
    change (if i.val=0 then CG.length Q g (j-1)-trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => Q) g (j-1)) else 0)=0
    rw [hcal0,sub_self,ite_self]
  have hF (i : Fin j) : ContDiffAt ℝ 1 (fun z => F z i) 0 :=
    (((hA j).sub (hA (j-1-i.val))).clm_apply (hreg.2.2.1 _ (by omega))).sub (hI _ (by omega))
  have hF0 (i : Fin j) : F 0 i=0 := by
    change (A 0 j-A 0 (j-1-i.val)) _-xrfcDImageError trial (A 0) g (j-1-i.val)=0
    rw [show A 0 j=A 0 (j-1-i.val) by simp only [hA0],sub_self,_root_.zero_apply,hI0 _ (by omega),sub_self]
  have hwbound (i : Fin j) : (fun z => w z i) =O[𝓝 0] (fun z => ‖z‖) := by
    simpa only [hw0 i,sub_zero] using ((hw i).differentiableAt (by norm_num)).isBigO_sub.norm_right
  have hFbound (i : Fin j) : (fun z => F z i) =O[𝓝 0] (fun z => ‖z‖) := by
    simpa only [hF0 i,sub_zero] using ((hF i).differentiableAt (by norm_num)).isBigO_sub.norm_right
  have hprod (i : Fin j) : (fun z => w z i • F z i) =O[𝓝 0] (fun z => ‖z‖^2) := by
    simpa only [smul_eq_mul,← sq] using (hwbound i).smul (hFbound i)
  have hsum : (fun z => ∑ i : Fin j,w z i • F z i) =O[𝓝 0] (fun z => ‖z‖^2) := by
    exact (IsBigO.sum (fun i (_ : i∈(Finset.univ : Finset (Fin j))) => hprod i)).congr_left
      (fun z => by simp only [Finset.sum_apply])
  have hti : (fun z => (tau z)⁻¹) =O[𝓝 0] (fun _ => (1 : ℝ)) :=
    ((htau.inv htau0).continuousAt.tendsto).isBigO_one ℝ
  have hresult : (fun z => (tau z)⁻¹ • ∑ i : Fin j,w z i • F z i) =O[𝓝 0] (fun z => ‖z‖^2) := by
    simpa only [smul_eq_mul,one_mul] using hti.smul hsum
  apply hresult.congr' ?_ EventuallyEq.rfl
  filter_upwards [htau.continuousAt.eventually_ne htau0] with z hz
  have he := congrArg (fun v : E => (tau z)⁻¹ • v) (xrfcD_image_error_recursion trial (A z) g j hz)
  change (tau z)⁻¹ • (tau z • xrfcDImageError trial (A z) g j)=
    (tau z)⁻¹ • ∑ i : Fin j,w z i • F z i at he
  have hzn : tau z≠0 := hz
  simpa only [smul_smul,inv_mul_cancel₀ hzn,one_smul] using he.symm

end
end krylov.OneGradient
