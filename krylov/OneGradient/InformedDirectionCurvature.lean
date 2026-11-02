import krylov.OneGradient.InformedRecordedComparison
import krylov.Methods.LineLengthComparison
import krylov.OneGradient.InformedNativeCurvature
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), true informed native D curvature jet.
Use: derive the actually selected history-only D trial error, keeping the
real measured native quotient and actual physical operator changes.
Source: the genuine recorded/native field comparison, actual positive
trial branch and reused primitive-C-one curvature freezing remainder.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Filter Topology Asymptotics krylov.Methods krylov.Reference krylov.Stability
open scoped InnerProductSpace
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual informed D selected trial differs quadratically from its
true native known-curvature quotient. All policy-field comparison and
positive-branch domains are derived from primitive operators.
Use: the real native error expansion uses the implemented history-only
trial rather than silently substituting a different D policy.
Article: main_krylov, thm:local(a), true informed D selected quotient.
Proof: the actual recorded virtual fields differ quadratically from the
native fields. Their line quotients preserve this order at the genuine
positive CG reference. Real quotient continuity keeps the true recorded
raw value positive, so the original selected trial equals that raw value. -/
theorem informed_native_direction_trial_quotient
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (hpre : ∀ i<N,CG.gradient (cgOperator base) g i≠0)
    (A : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : ∀ j,ContDiffAt ℝ 1 (fun z => A z j) 0) (hA0 : A 0=fun _ => cgOperator base)
    (k : ℕ) (hk : k<N) :
    let Q := cgOperator base
    let trial := informedTrial Q
    let H := fun z => oneGradientRun (xrfcDMethod fullMemory trial) (A z) g k
    let gv := fun z => xrfcNativeVirtualGradient true trial (A z) g k
    let d := fun z => xrfcNativeDirection true trial (A z) g k
    (fun z => trial (H z)-lineLength (gv z) (d z) (Q (d z))) =O[𝓝 0] (fun z => ‖z‖^2) := by
  dsimp only
  let Q := cgOperator base
  let trial := informedTrial Q
  let H := fun z => oneGradientRun (xrfcDMethod fullMemory trial) (A z) g k
  let gv := fun z => xrfcNativeVirtualGradient true trial (A z) g k
  let d := fun z => xrfcNativeDirection true trial (A z) g k
  let raw := fun z => lineLength (gv z) (d z) (Q (d z))
  let recg := fun z => virtualGradient (H z).pairs (H z).gradient
  let recd := fun z => windowDirection (H z).pairs (recg z)
  have hp := cgOperator_positive base hb
  have hdata := informed_native_virtual_data true base hb g N hpre A hA hA0 k hk.le
  have hgv0 : gv 0=CG.gradient Q g k := hdata.2.2.1
  have hd0 : d 0=CG.direction Q g k := hdata.2.2.2
  have hinv := CG.invariant Q hp.1 hp.2 g k (fun i hi => hpre i (hi.trans hk))
  have hdir := (CG.invariant_line_pos Q hp.2 g k hinv (hpre k hk)).1
  have hcurv : inner ℝ (d 0) (Q (d 0))≠0 := by rw [hd0];exact (hp.2 _ hdir).ne'
  have hraw : ContDiffAt ℝ 1 raw 0 := ((hdata.2.1.inner ℝ hdata.1).neg).div
    (hdata.2.1.inner ℝ (Q.contDiff.contDiffAt.comp 0 hdata.2.1)) hcurv
  have hraw0 : 0<raw 0 := by
    change 0<lineLength (gv 0) (d 0) (Q (d 0))
    rw [hgv0,hd0]
    exact (CG.invariant_line_pos Q hp.2 g k hinv (hpre k hk)).2.1
  have hfields := informed_native_recorded_fields_quadratic base hb g N hpre A hA hA0 k hk.le
  have hpow : Tendsto (fun z : X => ‖z‖^2) (𝓝 0) (𝓝 0) := by
    have hn : Tendsto (fun z : X => ‖z‖) (𝓝 0) (𝓝 0) := by simpa only [norm_zero] using continuous_norm.tendsto (0 : X)
    simpa only [zero_pow (by norm_num : (2 : ℕ)≠0)] using hn.pow 2
  have hdiff : (fun z => informedTrialLength Q (H z)-raw z) =O[𝓝 0] (fun z => ‖z‖^2) :=
    lineLength_difference_order Q recg recd gv d (gv 0) (d 0)
      hdata.1.continuousAt.tendsto hdata.2.1.continuousAt.tendsto hcurv _ hpow hfields.1 hfields.2
  have hr : Tendsto (fun z => informedTrialLength Q (H z)) (𝓝 0) (𝓝 (raw 0)) := by
    simpa only [sub_add_cancel,zero_add] using (hdiff.trans_tendsto hpow).add hraw.continuousAt.tendsto
  apply hdiff.congr' ?_ EventuallyEq.rfl
  filter_upwards [hr.eventually (lt_mem_nhds hraw0)] with z hz
  change informedTrialLength Q (H z)-raw z=trial (H z)-raw z
  rw [show trial (H z)=informedTrialLength Q (H z) from ite_eq_left hz]

/-- The actual implemented informed D error has the true frozen physical
curvature coefficient with a quadratic remainder from primitive C-one
operators. Every native field, selected branch and inverse domain is derived.
Use: complete the actual D unmeasured-pivot dictionary needed by the
original known-base output expansion and physical sharp-constant analysis.
Article: main_krylov, thm:local(a), genuine informed D curvature jet.
Proof: the real selected trial and native known-curvature quotient differ
quadratically. The measured native line length has a true positive CG
limit, so dividing preserves this error. Exact real line-error algebra
identifies the native quotient error with the actual curvature change.
Reuse the original primitive-C-one vanishing-middle curvature remainder. -/
theorem informed_native_direction_curvature_remainder
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (hpre : ∀ i<N,CG.gradient (cgOperator base) g i≠0)
    (A : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : ∀ j,ContDiffAt ℝ 1 (fun z => A z j) 0) (hA0 : A 0=fun _ => cgOperator base)
    (k : ℕ) (hk : k<N) :
    let Q := cgOperator base
    let d0 := CG.direction Q g k
    (fun z => xrfcNativeTrialError true (informedTrial Q) (A z) g k+
      inner ℝ d0 ((A z k-Q) d0)/inner ℝ d0 (Q d0)) =O[𝓝 0] (fun z => ‖z‖^2) := by
  let Q := cgOperator base
  let trial := informedTrial Q
  let H := fun z => oneGradientRun (xrfcDMethod fullMemory trial) (A z) g k
  let gv := fun z => xrfcNativeVirtualGradient true trial (A z) g k
  let d := fun z => xrfcNativeDirection true trial (A z) g k
  let raw := fun z => lineLength (gv z) (d z) (Q (d z))
  let ell := fun z => lineLength (gv z) (d z) (A z k (d z))
  have hp := cgOperator_positive base hb
  have hdata := informed_native_virtual_data true base hb g N hpre A hA hA0 k hk.le
  have hgv0 : gv 0=CG.gradient Q g k := hdata.2.2.1
  have hd0 : d 0=CG.direction Q g k := hdata.2.2.2
  have hinv := CG.invariant Q hp.1 hp.2 g k (fun i hi => hpre i (hi.trans hk))
  have hdir := (CG.invariant_line_pos Q hp.2 g k hinv (hpre k hk)).1
  have hcurv : inner ℝ (d 0) (Q (d 0))≠0 := by rw [hd0];exact (hp.2 _ hdir).ne'
  have hdesc : inner ℝ (d 0) (gv 0)≠0 := by
    rw [hd0,hgv0,hinv.search_pair]
    exact neg_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr (hpre k hk)))
  have hact : inner ℝ (d 0) (A 0 k (d 0))≠0 := by rw [congrFun hA0 k];exact hcurv
  have hell : ContDiffAt ℝ 1 ell 0 := ((hdata.2.1.inner ℝ hdata.1).neg).div
    (hdata.2.1.inner ℝ ((hA k).clm_apply hdata.2.1)) hact
  have hell0 : ell 0≠0 := by
    change lineLength (gv 0) (d 0) (A 0 k (d 0))≠0
    rw [congrFun hA0 k,hgv0,hd0]
    exact (CG.invariant_line_pos Q hp.2 g k hinv (hpre k hk)).2.1.ne'
  have hi : (fun z => (ell z)⁻¹) =O[𝓝 0] (fun _ => (1 : ℝ)) :=
    (hell.continuousAt.tendsto.inv₀ hell0).isBigO_one ℝ
  have ht := informed_native_direction_trial_quotient base hb g N hpre A hA hA0 k hk
  have hprod : (fun z => -(trial (H z)-raw z)*(ell z)⁻¹) =O[𝓝 0] (fun z => ‖z‖^2) := by
    simpa only [mul_one] using ht.neg_left.mul hi
  have heps : (fun z => xrfcNativeTrialError true trial (A z) g k-
      informedCurvatureError Q (A z k) (d z)) =O[𝓝 0] (fun z => ‖z‖^2) := by
    apply hprod.congr' ?_ EventuallyEq.rfl
    filter_upwards [(hdata.2.1.inner ℝ hdata.1).continuousAt.eventually_ne hdesc,
      (hdata.2.1.inner ℝ (Q.contDiff.contDiffAt.comp 0 hdata.2.1)).continuousAt.eventually_ne hcurv] with z hdz hqz
    have he : 1-raw z/ell z=informedCurvatureError Q (A z k) (d z) :=
      informed_length_error Q (A z k) (gv z) (d z) hdz hqz
    change -(trial (H z)-raw z)*(ell z)⁻¹=lastLaunchTrialError (trial (H z)) (d z) (gv z) (A z k)-_
    rw [lastLaunchTrialError_eq_relative,← he]
    change -(trial (H z)-raw z)*(ell z)⁻¹=(1-trial (H z)/ell z)-(1-raw z/ell z)
    simp only [div_eq_mul_inv]
    ring
  have hj := informed_curvature_c1_remainder Q (fun z => A z k) d (hA k) hdata.2.1
    (congrFun hA0 k) hcurv
  apply (heps.add hj).congr_left
  intro z
  rw [hd0]
  abel

end
end krylov.OneGradient
