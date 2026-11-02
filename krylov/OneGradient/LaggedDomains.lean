import krylov.Stability.LaggedRegularity
import krylov.OneGradient.LaggedReference
set_option autoImplicit false
/-!
Article: main_krylov, prop:hb, genuine lagged replay domains.
Use: discharge every replay inverse and measured-branch condition from the
actual nonstagnating positive quadratic execution in both original bases.
Source: the native XRFC basis invariants and the true observed CG dictionary.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability
open scoped InnerProductSpace
variable {m : ℕ}

/-- Both actual lagged windows have independent genuine steps and true
quadratic images on the entire nonstagnating reference prefix.
Use: all real lagged replay model domains follow from executed geometry.
Article: main_krylov, prop:hb.
Proof: the S invariant gives the actual stored basis; the original D replay
invariant identifies the real reconstructed window with the true CG window. -/
theorem lagged_reference_window (directions : Bool) {tau0 : ℝ} (htau0 : 0<tau0)
    (Q : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v,v≠0 → 0 < inner ℝ v (Q v))
    (g : EuclideanSpace ℝ (Fin m)) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (k : ℕ) (hk : k≤N) :
    let trial := laggedTrial directions tau0
    let H := oneGradientRun (xrfcBasisMethod directions trial) (fun _ => Q) g k
    let W := laggedWindow directions tau0 H
    LinearIndependent ℝ (windowSteps W) ∧ ∀ i,windowImages W i=Q (windowSteps W i) := by
  let trial : History (EuclideanSpace ℝ (Fin m)) → ℝ := laggedTrial directions tau0
  have ht (H : History (EuclideanSpace ℝ (Fin m))) : trial H≠0 :=
    (lagged_trial_positive directions htau0 H).ne'
  cases directions with
  | false =>
    exact ⟨(xrfc_full_basis trial Q hQ hpos g N hpre (fun _ _ => ht _) k hk).1,
      fun i => oneGradientRun_pairs_quadratic (xrfcMethod fullMemory trial) Q g k
        ((oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) g k).pairs.get i) (List.get_mem _ i)⟩
  | true =>
    let H := oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => Q) g k
    have hs := (xrfcD_state fullMemory trial Q hQ hpos g N hpre
      (fun _ _ hi => hi) (fun _ _ => ht _) k hk).1
    have hW : laggedWindow true tau0 H=directionWindow Q g k k := by
      rw [lagged_window_direction,selectedDirectionWindow,hs,oneGradientRun_length]
      rfl
    change LinearIndependent ℝ (windowSteps (laggedWindow true tau0 H)) ∧
      ∀ i,windowImages (laggedWindow true tau0 H) i=Q (windowSteps (laggedWindow true tau0 H) i)
    rw [hW]
    exact ⟨directionWindow_independent Q hQ hpos g k k (fun i hi => hpre i (hi.trans_le hk)),
      directionWindow_images Q g k k⟩

/-- The actual observed image reconstructed for a lagged decision is the
true CG direction image, and its measured length is the true CG line length.
Use: real positive branches and real measured-curvature domains are derived.
Article: main_krylov, prop:hb.
Proof: the genuine virtual point has its physical CG gradient; the actual
evaluated step adds precisely the chosen trial times the true direction. -/
theorem lagged_reference_measurement (directions : Bool) {tau0 : ℝ} (htau0 : 0<tau0)
    (Q : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v,v≠0 → 0 < inner ℝ v (Q v))
    (g : EuclideanSpace ℝ (Fin m)) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (k : ℕ) (hk : k<N) :
    let trial := laggedTrial directions tau0
    let method := xrfcBasisMethod directions trial
    let H := oneGradientRun method (fun _ => Q) g k
    let W := laggedWindow directions tau0 H
    let gv := virtualGradient W H.gradient
    let d := windowDirection W gv
    let q := (trial H)⁻¹ • (H.gradient+Q (method.step H)-gv)
    q=Q (CG.direction Q g k) ∧ inner ℝ d q≠0 ∧ lineLength gv d q=CG.length Q g k := by
  let trial : History (EuclideanSpace ℝ (Fin m)) → ℝ := laggedTrial directions tau0
  let method := xrfcBasisMethod directions trial
  let H := oneGradientRun method (fun _ => Q) g k
  let W := laggedWindow directions tau0 H
  let gv := virtualGradient W H.gradient
  let d := windowDirection W gv
  have hinputs := lagged_reference_inputs directions htau0 Q hQ hpos g N hpre k hk.le
  have hvg : gv=CG.gradient Q g k := hinputs.1
  have hd : d=CG.direction Q g k := hinputs.2.1
  have hsem : H.gradient+Q (virtualCorrection W H.gradient)=gv := hinputs.2.2.trans hvg.symm
  have ht : trial H≠0 := (lagged_trial_positive directions htau0 H).ne'
  have hstep : method.step H=virtualCorrection W H.gradient+trial H • d := by
    dsimp only [W,d,gv]
    cases directions with
    | false => rw [lagged_window_step];rfl
    | true => rw [lagged_window_direction];rfl
  have hprobe : (trial H)⁻¹ • (H.gradient+Q (method.step H)-gv)=Q d := by
    rw [hstep,map_add,map_smul,← add_assoc,hsem,add_sub_cancel_left,smul_smul,inv_mul_cancel₀ ht,one_smul]
  have hdne := (CG.invariant_line_pos Q hpos g k
    (CG.invariant Q hQ hpos g k (fun i hi => hpre i (hi.trans hk))) (hpre k hk)).1
  change (trial H)⁻¹ • (H.gradient+Q (method.step H)-gv)=Q (CG.direction Q g k) ∧
    inner ℝ d ((trial H)⁻¹ • (H.gradient+Q (method.step H)-gv))≠0 ∧
    lineLength gv d ((trial H)⁻¹ • (H.gradient+Q (method.step H)-gv))=CG.length Q g k
  rw [hprobe,hd]
  exact ⟨rfl,(hpos _ hdne).ne',by rw [hvg]⟩

/-- Every finite algebraic replay-domain condition holds on the actual
lagged quadratic history in either implemented basis.
Use: the actual lagged policy has no assumed smoothness or inverse domain.
Article: main_krylov, prop:hb.
Proof: chronological induction combines the genuine positive independent
window Gram matrices with the true observed positive CG line. -/
theorem lagged_reference_domain (directions : Bool) {tau0 : ℝ} (htau0 : 0<tau0)
    (Q : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v,v≠0 → 0 < inner ℝ v (Q v))
    (g : EuclideanSpace ℝ (Fin m)) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (k : ℕ) (hk : k≤N) :
    let method := xrfcBasisMethod directions (laggedTrial directions tau0)
    laggedReplayDomain directions tau0 g (oneGradientRun method (fun _ => Q) g k).records := by
  let method : OneGradientMethod (EuclideanSpace ℝ (Fin m)) :=
    xrfcBasisMethod directions (laggedTrial directions tau0)
  induction k with
  | zero => trivial
  | succ k ih =>
    let H := oneGradientRun method (fun _ => Q) g k
    let W := laggedWindow directions tau0 H
    have hw := lagged_reference_window directions htau0 Q hQ hpos g N hpre k (by omega)
    have hgram := (operatorGram_posDef Q hQ hpos hw.1).det_pos.ne'
    have hm : (windowModel W).det≠0 := by
      rw [windowModel_quadratic W Q hQ hw.2]
      exact hgram
    have hc : (crossGram (windowImages W) (windowSteps W)).det≠0 := by
      have he : windowImages W=fun i => Q (windowSteps W i) := funext hw.2
      rw [he]
      exact hgram
    have hobs := lagged_reference_measurement directions htau0 Q hQ hpos g N hpre k (by omega)
    have hp := (CG.invariant_line_pos Q hpos g k
      (CG.invariant Q hQ hpos g k (fun i hi => hpre i (by omega))) (hpre k (by omega))).2.1
    change laggedReplayDomain directions tau0 g
      (⟨0,0,method.step H,H.gradient+Q (method.step H),[]⟩::H.records)
    change laggedReplayDomain directions tau0 g H.records ∧ _
    refine ⟨ih (by omega),?_⟩
    have hinit : H.initial=g := oneGradientRun_initial method (fun _ => Q) g k
    rw [← hinit]
    exact ⟨hm,hc,(lagged_trial_positive directions htau0 H).ne',hobs.2.1,hobs.2.2.symm ▸ hp⟩

end
end krylov.OneGradient
