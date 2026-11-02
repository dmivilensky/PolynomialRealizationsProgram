import krylov.Stability.FullHistoryVirtual
import krylov.Stability.OneGradientTrialBridge
import krylov.OneGradient.XRFCTwoBasisOutput
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), genuine known-base informed XRFC policy.
Use: implement the original exact known-matrix curvature trial from actual
observed virtual data, derive exact reference values and primitive regularity.
Source: the real virtual-window solver, positive quadratic CG geometry and
shared complete observed-history calculus; no unobserved segment enters a decision. -/

namespace krylov.OneGradient
noncomputable section
open Matrix Filter Topology krylov.Reference krylov.Methods krylov.Stability krylov.Cancellation
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The informed trial uses the actual virtual gradient and direction and
the known fixed reference matrix action, before the new segment is observed.
Use: literal source policy for known-base comparisons.
Article: main_krylov, thm:local(a). -/
def informedTrialLength (known : E →L[ℝ] E) (H : History E) : ℝ :=
  let gv := virtualGradient H.pairs H.gradient
  let d := windowDirection H.pairs gv
  lineLength gv d (known d)

/-- A positive history-only totalization of the original informed trial.
Use: actual native S/D executions have nonzero trials on every supplied history.
Article: main_krylov, thm:local(a). -/
def informedTrial (known : E →L[ℝ] E) (H : History E) : ℝ :=
  if 0< informedTrialLength known H then informedTrialLength known H else 1

/-- The actual informed policy always selects a positive real trial.
Use: native basis and inverse domains follow from genuine execution.
Article: main_krylov, thm:local(a).
Proof: the real positive branch is used, or the policy returns one. -/
theorem informed_trial_positive (known : E →L[ℝ] E) (H : History E) : 0< informedTrial known H := by
  unfold informedTrial
  split_ifs with h
  · exact h
  · norm_num

/-- The true informed relative trial error is exactly the unmeasured
curvature change divided by the known curvature, for any actual descent pair.
Use: derive the source last-pivot term before taking its canonical expansion.
Article: main_krylov, thm:local(a).
Proof: cancel the genuine nonzero descent pairing in the ratio of the two
actual line lengths; linearity identifies the actual curvature difference. -/
theorem informed_length_error (known actual : E →L[ℝ] E) (g d : E)
    (hq : inner ℝ d g≠0) (hk : inner ℝ d (known d)≠0) :
    1-lineLength g d (known d)/lineLength g d (actual d)=
      -inner ℝ d ((actual-known) d)/inner ℝ d (known d) := by
  simp only [lineLength,_root_.sub_apply,inner_sub_right]
  field_simp
  ring

/-- Actual known-reference step-basis XRFC selects exactly every true CG
length under the genuine informed policy.
Use: all reference trial errors vanish for the implemented data-only rule.
Article: main_krylov, thm:local(a).
Proof: actual positive policy choices derive the true virtual CG gradient
and direction. The literal known-matrix curvature quotient is the true CG
length; positivity selects that original value in the actual policy. -/
theorem informed_trial_step_reference (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ i< N,CG.gradient Q g i≠0) (k : ℕ) (hk : k< N) :
    let H := oneGradientRun (xrfcMethod fullMemory (informedTrial Q)) (fun _ => Q) g k
    informedTrialLength Q H=CG.length Q g k ∧ informedTrial Q H=CG.length Q g k := by
  let H := oneGradientRun (xrfcMethod fullMemory (informedTrial Q)) (fun _ => Q) g k
  have hv := xrfc_full_reference (informedTrial Q) Q hQ hpos g N hpre
    (fun _ _ => (informed_trial_positive Q _).ne') k hk.le
  have he : informedTrialLength Q H=CG.length Q g k := by
    change lineLength (virtualGradient H.pairs H.gradient)
      (windowDirection H.pairs (virtualGradient H.pairs H.gradient))
      (Q (windowDirection H.pairs (virtualGradient H.pairs H.gradient)))=CG.length Q g k
    rw [hv.2.2,hv.2.1]
  have hp := (CG.invariant_line_pos Q hpos g k (CG.invariant Q hQ hpos g k
    (fun i hi => hpre i (hi.trans hk))) (hpre k hk)).2.1
  refine ⟨he,?_⟩
  change (if 0< informedTrialLength Q H then informedTrialLength Q H else 1)=_
  rw [he,ite_eq_left hp]

/-- The actual positive informed policy has primitive C-r full-history
charts at any true virtual-solve domain with positive selected raw value.
Use: this proves regularity of the observed policy itself, not of a prescribed
trial sequence or an assumed smooth trajectory.
Article: main_krylov, thm:local(a) and lem:U(d).
Proof: the shared real complete-history calculus gives the actual virtual
gradient and direction; positive known curvature permits its real quotient.
The proved raw positivity keeps the actual positive branch on a neighborhood. -/
theorem informed_trial_history_regular [CompleteSpace E] (known : E →L[ℝ] E)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (known v)) (H : History E) (r : WithTop ℕ∞)
    (hM : (windowModel H.pairs).det≠0)
    (hC : (crossGram (windowImages H.pairs) (windowSteps H.pairs)).det≠0)
    (hraw : 0< informedTrialLength known H) :
    ContDiffAt ℝ r (historyEstimateChart (informedTrial known) H.queryShape H.observationList.length)
      (observedArray H.observationList.length H.observationList) := by
  let x := observedArray H.observationList.length H.observationList
  let Hc := fun z : Fin H.observationList.length → E => historyFromObservations H.queryShape (List.ofFn z)
  let gv := fun z => virtualGradient (Hc z).pairs (Hc z).gradient
  let d := fun z => windowDirection (Hc z).pairs (gv z)
  have hb := full_history_virtual_contDiffAt H r hM hC
  have hH : Hc x=H := by
    change historyFromObservations H.queryShape (List.ofFn (observedArray _ H.observationList))=H
    rw [ofFn_observedArray,historyFromObservations_actual]
  have hd0 : d x≠0 := by
    intro hz
    have hz' : informedTrialLength known H=0 := by
      rw [← hH]
      change lineLength (gv x) (d x) (known (d x))=0
      simp only [lineLength,hz,inner_zero_left,neg_zero,zero_div]
    exact hraw.ne' hz'
  have hden : inner ℝ (d x) (known (d x))≠0 := (hpos _ hd0).ne'
  have hreg : ContDiffAt ℝ r (historyEstimateChart (informedTrialLength known) H.queryShape H.observationList.length) x :=
    ((hb.2.2.inner ℝ hb.2.1).neg).div (hb.2.2.inner ℝ (known.contDiff.contDiffAt.comp x hb.2.2)) hden
  have hrawc : 0< historyEstimateChart (informedTrialLength known) H.queryShape H.observationList.length x := by
    change 0< informedTrialLength known (Hc x)
    rw [hH]
    exact hraw
  apply hreg.congr_of_eventuallyEq
  filter_upwards [hreg.continuousAt.eventually (isOpen_Ioi.mem_nhds hrawc)] with z hz
  exact ite_eq_left hz

/-- On every actual active quadratic prefix, the informed policy uses its
original positive raw known-curvature quotient, even when the true reference
operator differs from the known base.
Use: the genuine known-base comparison is calibrated at the actual A0
reference rather than silently replacing it by the known matrix.
Article: main_krylov, thm:local(a).
Proof: actual positive policy choices derive the real virtual CG inputs of
the true reference. Their descent is strictly positive and the known positive
matrix has positive curvature on the genuine nonzero CG direction. -/
theorem informed_trial_quadratic_values (known Q : E →L[ℝ] E)
    (hknown : ∀ v : E,v≠0 → 0 < inner ℝ v (known v)) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0) (k : ℕ) (hk : k<N) :
    let H := oneGradientRun (xrfcMethod fullMemory (informedTrial known)) (fun _ => Q) g k
    0 < informedTrialLength known H ∧ informedTrial known H=informedTrialLength known H ∧
      1-informedTrial known H/CG.length Q g k=
        -inner ℝ (CG.direction Q g k) ((Q-known) (CG.direction Q g k))/
          inner ℝ (CG.direction Q g k) (known (CG.direction Q g k)) := by
  let H := oneGradientRun (xrfcMethod fullMemory (informedTrial known)) (fun _ => Q) g k
  have hv := xrfc_full_reference (informedTrial known) Q hQ hpos g N hpre
    (fun _ _ => (informed_trial_positive known _).ne') k hk.le
  have hInv := CG.invariant Q hQ hpos g k (fun i hi => hpre i (hi.trans hk))
  have hd := (CG.invariant_line_pos Q hpos g k hInv (hpre k hk)).1
  have hden : 0 < inner ℝ (CG.direction Q g k) (known (CG.direction Q g k)) := hknown _ hd
  have hraw : informedTrialLength known H=
      lineLength (CG.gradient Q g k) (CG.direction Q g k) (known (CG.direction Q g k)) := by
    change lineLength (virtualGradient H.pairs H.gradient)
      (windowDirection H.pairs (virtualGradient H.pairs H.gradient))
      (known (windowDirection H.pairs (virtualGradient H.pairs H.gradient)))=_
    rw [hv.2.2,hv.2.1]
  have hp : 0 < informedTrialLength known H := by
    rw [hraw,lineLength,hInv.search_pair,neg_neg]
    exact div_pos (sq_pos_of_pos (norm_pos_iff.mpr (hpre k hk))) hden
  have he : informedTrial known H=informedTrialLength known H := ite_eq_left hp
  refine ⟨hp,he,?_⟩
  rw [he,hraw]
  apply informed_length_error
  · rw [hInv.search_pair]
    exact neg_ne_zero.mpr (sq_pos_of_pos (norm_pos_iff.mpr (hpre k hk))).ne'
  · exact hden.ne'

end
end krylov.OneGradient
