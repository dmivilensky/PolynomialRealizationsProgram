import krylov.OneGradient.NativeLastLaunch
import krylov.OneGradient.InformedExactQueries
import krylov.Stability.XRFCModelDomains
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), exact both-native calibrated reference data.
Use: derive the actual incoming gradient, old basis, observed images,
inverse domains and vanishing projected residual in either native basis.
Source: genuine informed CG calibration and true complete quadratic
S/D history equivalence, actual array domains and real CG orthogonality.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Methods krylov.Reference krylov.Stability
open scoped InnerProductSpace
variable {n : ℕ}

/-- Every actual informed reference evaluated gradient equals the true
CG gradient, in either native implementation and through every real prefix.
Use: reference calibration concerns the actual incoming observation.
Article: main_krylov, thm:local(a), genuine native reference gradient.
Proof: the actual informed S evaluated point is exactly CG. The true
quadratic gradient balance gives its real gradient; exact full S/D
reference history equality gives the identical D observation. -/
theorem informed_native_reference_gradient (directions : Bool)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v,v≠0 → 0< inner ℝ v (Q v))
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (k : ℕ) (hk : k≤ N) :
    oneGradientGradient (xrfcBasisMethod directions (informedTrial Q)) (fun _ => Q) g k=CG.gradient Q g k := by
  have ht : ∀ i<N,informedTrial Q (oneGradientRun (xrfcMethod fullMemory (informedTrial Q)) (fun _ => Q) g i)≠0 :=
    fun _ _ => (informed_trial_positive Q _).ne'
  have hS : oneGradientGradient (xrfcMethod fullMemory (informedTrial Q)) (fun _ => Q) g k=CG.gradient Q g k := by
    rw [oneGradientGradient,oneGradientRun_quadratic_gradient,
      informed_reference_evaluated Q hQ hpos g N hpre k hk,← CG.gradient_displacement]
  cases directions with
  | false => exact hS
  | true =>
    change (oneGradientRun (xrfcDMethod fullMemory (informedTrial Q)) (fun _ => Q) g k).gradient=_
    rw [xrfc_quadratic_basis_histories (informedTrial Q) Q hQ hpos g N hpre ht k hk]
    exact hS

/-- Every actual old native informed reference column is the real CG
direction with its genuine basis scale: alpha for S and one for D.
Use: normalize the actual incoming coordinate equations in the true CG frame.
Article: main_krylov, thm:local(a), actual native reference columns.
Proof: the informed S query is the true CG step; genuine quadratic D
replay gives the actual CG direction independently of its trial scale. -/
theorem informed_native_reference_column (directions : Bool)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v,v≠0 → 0< inner ℝ v (Q v))
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (k : ℕ) (hk : k≤ N) (i : Fin k) :
    xrfcNativeColumns directions (informedTrial Q) (fun _ => Q) g k i=
      (if directions then (1 : ℝ) else CG.length Q g (k-1-i.val)) • CG.direction Q g (k-1-i.val) := by
  cases directions with
  | false => exact informed_reference_step Q hQ hpos g N hpre _ (by omega)
  | true =>
    change xrfcDExecutedDirection (informedTrial Q) (fun _ => Q) g (k-1-i.val)=1 • _
    rw [one_smul]
    exact xrfcD_executed_direction_reference (informedTrial Q) Q hQ hpos g N hpre
      (fun _ _ => (informed_trial_positive Q _).ne') _ (by omega)

/-- Every actual native informed reference image is its true known
quadratic operator action on the same actual old native column.
Use: all genuine model differences vanish at the true reference.
Article: main_krylov, thm:local(a), true native reference images.
Proof: S images are their real queried actions. D replay is proved exact
on genuine quadratic histories and uses its true CG direction. -/
theorem informed_native_reference_image (directions : Bool)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v,v≠0 → 0< inner ℝ v (Q v))
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (k : ℕ) (hk : k≤ N) (i : Fin k) :
    xrfcNativeImages directions (informedTrial Q) (fun _ => Q) g k i=
      Q (xrfcNativeColumns directions (informedTrial Q) (fun _ => Q) g k i) := by
  cases directions with
  | false => rfl
  | true =>
    change xrfcDExecutedImage (informedTrial Q) (fun _ => Q) g (k-1-i.val)=
      Q (xrfcDExecutedDirection (informedTrial Q) (fun _ => Q) g (k-1-i.val))
    rw [xrfcD_executed_image_reference (informedTrial Q) Q hQ hpos g N hpre
      (fun _ _ => (informed_trial_positive Q _).ne') _ (by omega),
      xrfcD_executed_direction_reference (informedTrial Q) Q hQ hpos g N hpre
        (fun _ _ => (informed_trial_positive Q _).ne') _ (by omega)]

/-- Both actual finite old native solve matrices are nonsingular at
every real informed reference prefix, including the full final model.
Use: every eventual native row-calculus inverse domain is derived.
Article: main_krylov, thm:local(a), genuine native reference solve domains.
Proof: apply the proved true S or D executed-array domain theorem with
the actual always-positive informed trial on its genuine reference histories. -/
theorem informed_native_reference_domains (directions : Bool)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v,v≠0 → 0< inner ℝ v (Q v))
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (k : ℕ) (hk : k≤ N) :
    let s := xrfcNativeColumns directions (informedTrial Q) (fun _ => Q) g k
    let y := xrfcNativeImages directions (informedTrial Q) (fun _ => Q) g k
    (crossGram y s).det≠0 ∧ (pairModel s y).det≠0 := by
  cases directions with
  | false =>
    exact xrfc_full_array_domains (informedTrial Q) Q hQ hpos g N hpre
      (fun _ _ => (informed_trial_positive Q _).ne') k hk
  | true =>
    exact xrfcD_full_array_domains (informedTrial Q) Q hQ hpos g N hpre
      (fun _ _ => (informed_trial_positive Q _).ne') k hk

/-- The actual old native projected informed gradient is zero at the
true quadratic reference, in either basis and every actual prefix.
Use: the real virtual correction weights vanish by their computed solve.
Article: main_krylov, thm:local(a), genuine calibrated zero weights.
Proof: the true observed gradient is CG and every actual old column is
a genuine multiple of an earlier CG direction. The actual CG invariant
annihilates every such old direction. -/
theorem informed_native_reference_orthogonal (directions : Bool)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v,v≠0 → 0< inner ℝ v (Q v))
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (k : ℕ) (hk : k≤ N) :
    coordinates (xrfcNativeColumns directions (informedTrial Q) (fun _ => Q) g k)
      (oneGradientGradient (xrfcBasisMethod directions (informedTrial Q)) (fun _ => Q) g k)=0 := by
  rw [informed_native_reference_gradient directions Q hQ hpos g N hpre k hk]
  ext i
  change inner ℝ (xrfcNativeColumns directions (informedTrial Q) (fun _ => Q) g k i) (CG.gradient Q g k)=0
  rw [informed_native_reference_column directions Q hQ hpos g N hpre k hk i,real_inner_smul_left,
    (CG.invariant Q hQ hpos g k (fun i hi => hpre i (hi.trans_le hk))).old_direction _ (by omega),mul_zero]

end
end krylov.OneGradient
