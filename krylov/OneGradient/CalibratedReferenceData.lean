import krylov.OneGradient.CalibratedNativeReference
import krylov.OneGradient.InformedNativeReference
import krylov.OneGradient.InformedNativeCalibration
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), general actual calibrated native data.
Use: derive the real reference gradients, steps, observed images, model
domains and orthogonality for arbitrary calibrated history-only rules.
Source: genuine quadratic full-memory S/D consistency and complete
history equivalence, with exact actual CG trial calibration.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Methods krylov.Reference krylov.Stability
open scoped InnerProductSpace
variable {n : ℕ}

/-- Every actual calibrated native reference trial is genuinely nonzero.
Use: derive quadratic replay and model domains from true CG activity.
Article: main_krylov, thm:local(a).
Proof: calibration gives the true strictly positive active CG length. -/
theorem calibrated_native_reference_nonzero (directions : Bool)
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v,v≠0 → 0 < inner ℝ v (Q v))
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (hcal : CalibratedTrial trial Q g N) (i : ℕ) (hi : i<N) :
    trial (oneGradientRun (xrfcBasisMethod directions trial) (fun _ => Q) g i)≠0 := by
  rw [calibrated_native_reference_trial directions trial Q hQ hpos g N hpre hcal i hi]
  exact (CG.invariant_line_pos Q hpos g i (CG.invariant Q hQ hpos g i (fun j hj => hpre j (hj.trans hi))) (hpre i hi)).2.1.ne'

/-- Every actual calibrated S reference step equals its true CG step.
Use: no reference physical trajectory is postulated in the general theorem.
Article: main_krylov, thm:local(a).
Proof: subtract the genuine consecutive evaluated-point identities and
use the actual CG point recursion. -/
theorem calibrated_reference_step
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v,v≠0 → 0 < inner ℝ v (Q v))
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (hcal : CalibratedTrial trial Q g N) (k : ℕ) (hk : k<N) :
    oneGradientStep (xrfcMethod fullMemory trial) (fun _ => Q) g k=referenceStep Q g k := by
  have hnext := calibrated_reference_evaluated trial Q hQ hpos g N hpre hcal (k+1) (by omega)
  have hold := calibrated_reference_evaluated trial Q hQ hpos g N hpre hcal k hk.le
  rw [CG.displacement_succ] at hnext
  change oneGradientStep (xrfcMethod fullMemory trial) (fun _ => Q) g k+
    (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) g k).displacement=_ at hnext
  rw [hold] at hnext
  exact add_right_cancel (hnext.trans (add_comm _ _))

/-- Every actual calibrated reference evaluated gradient equals the true
CG gradient, in either native implementation and through every real prefix.
Use: reference calibration concerns the actual incoming observation.
Article: main_krylov, thm:local(a), genuine native reference gradient.
Proof: the actual calibrated S evaluated point is exactly CG. The true
quadratic gradient balance gives its real gradient; exact full S/D
reference history equality gives the identical D observation. -/
theorem calibrated_native_reference_gradient (directions : Bool)
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v,v≠0 → 0< inner ℝ v (Q v))
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (hcal : CalibratedTrial trial Q g N)
    (k : ℕ) (hk : k≤ N) :
    oneGradientGradient (xrfcBasisMethod directions trial) (fun _ => Q) g k=CG.gradient Q g k := by
  have ht : ∀ i<N,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) g i)≠0 :=
    calibrated_native_reference_nonzero false trial Q hQ hpos g N hpre hcal
  have hS : oneGradientGradient (xrfcMethod fullMemory trial) (fun _ => Q) g k=CG.gradient Q g k := by
    rw [oneGradientGradient,oneGradientRun_quadratic_gradient,
      calibrated_reference_evaluated trial Q hQ hpos g N hpre hcal k hk,← CG.gradient_displacement]
  cases directions with
  | false => exact hS
  | true =>
    change (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => Q) g k).gradient=_
    rw [xrfc_quadratic_basis_histories trial Q hQ hpos g N hpre ht k hk]
    exact hS

/-- Every actual old native calibrated reference column is the real CG
direction with its genuine basis scale: alpha for S and one for D.
Use: normalize the actual incoming coordinate equations in the true CG frame.
Article: main_krylov, thm:local(a), actual native reference columns.
Proof: the calibrated S query is the true CG step; genuine quadratic D
replay gives the actual CG direction independently of its trial scale. -/
theorem calibrated_native_reference_column (directions : Bool)
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v,v≠0 → 0< inner ℝ v (Q v))
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (hcal : CalibratedTrial trial Q g N)
    (k : ℕ) (hk : k≤ N) (i : Fin k) :
    xrfcNativeColumns directions trial (fun _ => Q) g k i=
      (if directions then (1 : ℝ) else CG.length Q g (k-1-i.val)) • CG.direction Q g (k-1-i.val) := by
  cases directions with
  | false => exact calibrated_reference_step trial Q hQ hpos g N hpre hcal _ (by omega)
  | true =>
    change xrfcDExecutedDirection trial (fun _ => Q) g (k-1-i.val)=1 • _
    rw [one_smul]
    exact xrfcD_executed_direction_reference trial Q hQ hpos g N hpre
      (calibrated_native_reference_nonzero true trial Q hQ hpos g N hpre hcal) _ (by omega)

/-- Every actual native calibrated reference image is its true known
quadratic operator action on the same actual old native column.
Use: all genuine model differences vanish at the true reference.
Article: main_krylov, thm:local(a), true native reference images.
Proof: S images are their real queried actions. D replay is proved exact
on genuine quadratic histories and uses its true CG direction. -/
theorem calibrated_native_reference_image (directions : Bool)
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v,v≠0 → 0< inner ℝ v (Q v))
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (hcal : CalibratedTrial trial Q g N)
    (k : ℕ) (hk : k≤ N) (i : Fin k) :
    xrfcNativeImages directions trial (fun _ => Q) g k i=
      Q (xrfcNativeColumns directions trial (fun _ => Q) g k i) := by
  cases directions with
  | false => rfl
  | true =>
    change xrfcDExecutedImage trial (fun _ => Q) g (k-1-i.val)=
      Q (xrfcDExecutedDirection trial (fun _ => Q) g (k-1-i.val))
    rw [xrfcD_executed_image_reference trial Q hQ hpos g N hpre
      (calibrated_native_reference_nonzero true trial Q hQ hpos g N hpre hcal) _ (by omega),
      xrfcD_executed_direction_reference trial Q hQ hpos g N hpre
        (calibrated_native_reference_nonzero true trial Q hQ hpos g N hpre hcal) _ (by omega)]

/-- Both actual finite old native solve matrices are nonsingular at
every real calibrated reference prefix, including the full final model.
Use: every eventual native row-calculus inverse domain is derived.
Article: main_krylov, thm:local(a), genuine native reference solve domains.
Proof: apply the proved true S or D executed-array domain theorem with
the actual always-positive calibrated trial on its genuine reference histories. -/
theorem calibrated_native_reference_domains (directions : Bool)
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v,v≠0 → 0< inner ℝ v (Q v))
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (hcal : CalibratedTrial trial Q g N)
    (k : ℕ) (hk : k≤ N) :
    let s := xrfcNativeColumns directions trial (fun _ => Q) g k
    let y := xrfcNativeImages directions trial (fun _ => Q) g k
    (crossGram y s).det≠0 ∧ (pairModel s y).det≠0 := by
  cases directions with
  | false =>
    exact xrfc_full_array_domains trial Q hQ hpos g N hpre
      (calibrated_native_reference_nonzero false trial Q hQ hpos g N hpre hcal) k hk
  | true =>
    exact xrfcD_full_array_domains trial Q hQ hpos g N hpre
      (calibrated_native_reference_nonzero true trial Q hQ hpos g N hpre hcal) k hk

/-- The actual old native projected calibrated gradient is zero at the
true quadratic reference, in either basis and every actual prefix.
Use: the real virtual correction weights vanish by their computed solve.
Article: main_krylov, thm:local(a), genuine calibrated zero weights.
Proof: the true observed gradient is CG and every actual old column is
a genuine multiple of an earlier CG direction. The actual CG invariant
annihilates every such old direction. -/
theorem calibrated_native_reference_orthogonal (directions : Bool)
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v,v≠0 → 0< inner ℝ v (Q v))
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (hcal : CalibratedTrial trial Q g N)
    (k : ℕ) (hk : k≤ N) :
    coordinates (xrfcNativeColumns directions trial (fun _ => Q) g k)
      (oneGradientGradient (xrfcBasisMethod directions trial) (fun _ => Q) g k)=0 := by
  rw [calibrated_native_reference_gradient directions trial Q hQ hpos g N hpre hcal k hk]
  ext i
  change inner ℝ (xrfcNativeColumns directions trial (fun _ => Q) g k i) (CG.gradient Q g k)=0
  rw [calibrated_native_reference_column directions trial Q hQ hpos g N hpre hcal k hk i,real_inner_smul_left,
    (CG.invariant Q hQ hpos g k (fun i hi => hpre i (hi.trans_le hk))).old_direction _ (by omega),mul_zero]

/-- The actual reference native old arrays compute precisely the true
CG direction from their real CG incoming gradient, in either basis.
Use: no last-direction value is postulated in the incoming coefficient.
Article: main_krylov, thm:local(a), true native direction calibration.
Proof: the actual array conjugacy solve is its original S or D window
solve; genuine quadratic virtual consistency identifies that real solve. -/
theorem calibrated_native_reference_direction (directions : Bool)
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v,v≠0 → 0< inner ℝ v (Q v))
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (hcal : CalibratedTrial trial Q g N)
    (k : ℕ) (hk : k≤ N) :
    conjugacyDirection (xrfcNativeColumns directions trial (fun _ => Q) g k)
      (xrfcNativeImages directions trial (fun _ => Q) g k) (CG.gradient Q g k)=CG.direction Q g k := by
  cases directions with
  | false =>
    let m := xrfcMethod fullMemory trial
    let H := oneGradientRun m (fun _ => Q) g k
    have hv := xrfc_full_reference trial Q hQ hpos g N hpre (calibrated_native_reference_nonzero false trial Q hQ hpos g N hpre hcal) k hk
    have href : windowDirection H.pairs (CG.gradient Q g k)=CG.direction Q g k := by
      rw [← hv.2.1]
      exact hv.2.2
    have hd := oneGradient_full_direction_coordinates m (fun _ => Q) g (CG.gradient Q g k) k
    rw [selectedWindow_full] at hd
    exact hd.symm.trans href
  | true =>
    have hv := (xrfcD_reference fullMemory trial Q hQ hpos g N hpre (fun _ _ hi => hi)
      (calibrated_native_reference_nonzero true trial Q hQ hpos g N hpre hcal) k hk).2.1
    change xrfcDVirtualGradient trial (fun _ => Q) g k=CG.gradient Q g k at hv
    have hd := xrfcD_direction_coordinates trial (fun _ => Q) g k
    rw [hv,xrfcD_executed_direction_reference trial Q hQ hpos g N hpre
      (calibrated_native_reference_nonzero true trial Q hQ hpos g N hpre hcal) k hk] at hd
    exact hd.symm


end
end krylov.OneGradient
