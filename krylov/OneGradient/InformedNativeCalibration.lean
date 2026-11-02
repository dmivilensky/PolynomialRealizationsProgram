import krylov.OneGradient.InformedNativeReference
import krylov.OneGradient.InformedDirectionError
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), genuine native final-launch calibration.
Use: supply actual calibrated trial/direction values and original native
image errors to the primitive both-row incoming-gradient theorem.
Source: true full S/D quadratic consistency and history equivalence,
genuine informed trial calibration and actual quadratic replay error.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Methods krylov.Reference
open Filter Topology Asymptotics
open scoped InnerProductSpace
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual reference native old arrays compute precisely the true
CG direction from their real CG incoming gradient, in either basis.
Use: no last-direction value is postulated in the incoming coefficient.
Article: main_krylov, thm:local(a), true native direction calibration.
Proof: the actual array conjugacy solve is its original S or D window
solve; genuine quadratic virtual consistency identifies that real solve. -/
theorem informed_native_reference_direction (directions : Bool)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v,v≠0 → 0< inner ℝ v (Q v))
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (k : ℕ) (hk : k≤ N) :
    conjugacyDirection (xrfcNativeColumns directions (informedTrial Q) (fun _ => Q) g k)
      (xrfcNativeImages directions (informedTrial Q) (fun _ => Q) g k) (CG.gradient Q g k)=CG.direction Q g k := by
  let trial := informedTrial Q
  cases directions with
  | false =>
    let m := xrfcMethod fullMemory trial
    let H := oneGradientRun m (fun _ => Q) g k
    have hv := xrfc_full_reference trial Q hQ hpos g N hpre (fun _ _ => (informed_trial_positive Q _).ne') k hk
    have href : windowDirection H.pairs (CG.gradient Q g k)=CG.direction Q g k := by
      rw [← hv.2.1]
      exact hv.2.2
    have hd := oneGradient_full_direction_coordinates m (fun _ => Q) g (CG.gradient Q g k) k
    rw [selectedWindow_full] at hd
    exact hd.symm.trans href
  | true =>
    have hv := (xrfcD_reference fullMemory trial Q hQ hpos g N hpre (fun _ _ hi => hi)
      (fun _ _ => (informed_trial_positive Q _).ne') k hk).2.1
    change xrfcDVirtualGradient trial (fun _ => Q) g k=CG.gradient Q g k at hv
    have hd := xrfcD_direction_coordinates trial (fun _ => Q) g k
    rw [hv,xrfcD_executed_direction_reference trial Q hQ hpos g N hpre
      (fun _ _ => (informed_trial_positive Q _).ne') k hk] at hd
    exact hd.symm

/-- The actual selected informed reference trial is the true CG length
on the genuine complete history in either native basis.
Use: final reference calibration is derived for the real policy.
Article: main_krylov, thm:local(a), true native trial calibration.
Proof: the actual informed S trial is calibrated; genuine complete D/S
reference history equality preserves that same history-only decision. -/
theorem informed_native_reference_trial (directions : Bool)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v,v≠0 → 0< inner ℝ v (Q v))
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (k : ℕ) (hk : k<N) :
    informedTrial Q (oneGradientRun (xrfcBasisMethod directions (informedTrial Q)) (fun _ => Q) g k)=CG.length Q g k := by
  cases directions with
  | false => exact (informed_trial_step_reference Q hQ hpos g N hpre k hk).2
  | true =>
    change informedTrial Q (oneGradientRun (xrfcDMethod fullMemory (informedTrial Q)) (fun _ => Q) g k)=_
    rw [xrfc_quadratic_basis_histories (informedTrial Q) Q hQ hpos g N hpre
      (fun _ _ => (informed_trial_positive Q _).ne') k hk.le]
    exact (informed_trial_step_reference Q hQ hpos g N hpre k hk).2

/-- The actual old native images differ quadratically from their real
own-segment operator images, in either implemented basis. The S difference
is identically zero; the D difference is its genuine proved native replay error.
Use: every image-error premise of the true incoming row calculus is derived.
Article: main_krylov, thm:local(a), native old image-error order.
Proof: expand the literal S observed image or use the original calibrated
informed D replay theorem, at the real newest-age chronological index. -/
theorem informed_native_image_error (directions : Bool)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hpre : ∀ i<N,CG.gradient (cgOperator base) g i≠0)
    (A : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : ∀ j,ContDiffAt ℝ 1 (fun z => A z j) 0) (hA0 : A 0=fun _ => cgOperator base)
    (k : ℕ) (hk : k≤ N) (i : Fin k) :
    (fun z => xrfcNativeImages directions (informedTrial (cgOperator base)) (A z) g k i-
      A z (k-1-i.val) (xrfcNativeColumns directions (informedTrial (cgOperator base)) (A z) g k i))
        =O[𝓝 0] (fun z => ‖z‖^2) := by
  cases directions with
  | false =>
    have hz : (fun _ : X => (0 : EuclideanSpace ℝ (Fin n))) =O[𝓝 0] (fun z => ‖z‖^2) := isBigO_zero _ _
    simpa only [xrfcNativeColumns,xrfcNativeImages,Bool.false_eq_true,ite_false,sub_self] using hz
  | true => exact informed_direction_image_quadratic base hb g N hpre A hA hA0 _ (by omega)

end
end krylov.OneGradient
