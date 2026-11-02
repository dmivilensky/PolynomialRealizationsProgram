import krylov.OneGradient.CalibratedDirectionError
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), actual calibrated replay contribution.
Use: the actual terminal native virtual coefficients multiply true quadratic
image errors into a genuine cubic contribution in the full parameter.
Source: derived primitive native coefficient calculus, genuine exact-reference
calibration and the proved actual quadratic direction-image theorem.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Methods krylov.Reference krylov.Stability
open Filter Topology Asymptotics
open scoped BigOperators
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The genuine complete native direction-image contribution, with the
actual computed virtual coefficients and actual replay errors, has cubic
order under primitive C-one data and true reference trial calibration.
Use: derive the original known-base direction-image contribution order;
neither coefficient rates nor a quadratic replay-error field is supplied.
Article: main_krylov, thm:local(a), direction-basis O(omega³) contribution.
Proof: actual reference calibration makes every native virtual coefficient
zero. Primitive native C-one solve regularity gives first-order coefficients;
the proved true replay theorem gives quadratic actual image errors. Each
genuine product is cubic and the finite native sum has that same order. -/
theorem calibrated_direction_image_contribution_cubic
    (trial : History E → ℝ) (A : X → ℕ → E →L[ℝ] E)
    (hA : ∀ i,ContDiffAt ℝ 1 (fun z => A z i) 0)
    (Q : E →L[ℝ] E) (hA0 : A 0=fun _ => Q) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (N : ℕ)
    (hpre : ∀ i< N,CG.gradient Q g i≠0)
    (ht : ∀ i< N,trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => Q) g i)≠0)
    (hcal : ∀ i< N,trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => Q) g i)=CG.length Q g i)
    (hT : ∀ k< N,ContDiffAt ℝ 1 (trialCoordinate trial k)
      (oneGradientData (xrfcDMethod fullMemory trial) (fun _ => Q) g k))
    (k : ℕ) (hk : k≤ N) :
    (fun z => ∑ i : Fin k,xrfcDArrayCoefficients trial (A z) g k i •
      xrfcDImageError trial (A z) g (k-1-i.val)) =O[𝓝 0] (fun z => ‖z‖^3) := by
  have hcharts : ∀ j< N,ContDiffAt ℝ 1 (trialCoordinate trial j)
      (oneGradientData (xrfcDMethod fullMemory trial) (A 0) g j) := by rw [hA0];exact hT
  have hprod (i : Fin k) : (fun z => xrfcDArrayCoefficients trial (A z) g k i •
      xrfcDImageError trial (A z) g (k-1-i.val)) =O[𝓝 0] (fun z => ‖z‖^3) := by
    have hkp : 0< k := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
    have hreg := quadraticXRFCD_coefficients_contDiffAt trial A (fun _ => g) 0 hA contDiffAt_const
      Q hA0 hQ hpos N hpre ht hcharts k hk i
    have hzero : xrfcDArrayCoefficients trial (A 0) g k i=0 := by
      rw [hA0,xrfcD_reference_coefficients_at trial Q hQ hpos g N hpre ht k hk hkp]
      have hcal0 := hcal (k-1) (by omega)
      change (if i.val=0 then CG.length Q g (k-1)-trial
        (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => Q) g (k-1)) else 0)=0
      rw [hcal0,sub_self,ite_self]
    have hw : (fun z => xrfcDArrayCoefficients trial (A z) g k i) =O[𝓝 0] (fun z => ‖z‖) := by
      simpa only [hzero,sub_zero] using (hreg.differentiableAt (by norm_num)).isBigO_sub.norm_right
    have hi := calibrated_direction_image_quadratic trial A hA Q hA0 hQ hpos g N hpre ht hcal hT
      (k-1-i.val) (by omega)
    exact (hw.smul hi).congr_right (fun z => by simp only [smul_eq_mul];ring)
  exact (IsBigO.sum (fun i (_ : i∈(Finset.univ : Finset (Fin k))) => hprod i)).congr_left
    (fun z => by simp only [Finset.sum_apply])

end
end krylov.OneGradient
