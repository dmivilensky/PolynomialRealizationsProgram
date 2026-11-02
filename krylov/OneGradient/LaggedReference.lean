import krylov.Methods.LaggedReplay
import krylov.OneGradient.XRFCTwoBasisOutput
set_option autoImplicit false
/-!
Article: main_krylov, prop:hb, true lagged reference measurements.
Use: derive the actual lagged decision from the original executed one-gradient
histories in both bases, with arbitrary positive initial trial.
Source: genuine native virtual CG geometry, actual replay dictionary and the
observed gradient-difference formula for the previous direction image.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Methods krylov.Reference
open scoped InnerProductSpace
variable {m : ℕ}

/-- The genuine lagged method computes the original virtual CG inputs in
its actual selected basis; its virtual point has the true semantic gradient.
Use: no reference trial values or unobserved direction images are assumed.
Article: main_krylov, prop:hb.
Proof: global positivity of the real chronological policy gives every native
basis domain. The original two native reference theorems identify the actual
virtual point, gradient and direction, and true quadratic semantics gives its
original physical gradient identity. -/
theorem lagged_reference_inputs (directions : Bool) {tau0 : ℝ} (htau0 : 0<tau0)
    (Q : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v,v≠0 → 0 < inner ℝ v (Q v))
    (g : EuclideanSpace ℝ (Fin m)) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (k : ℕ) (hk : k≤N) :
    let trial : History (EuclideanSpace ℝ (Fin m)) → ℝ := laggedTrial directions tau0
    let method := xrfcBasisMethod directions trial
    let H := oneGradientRun method (fun _ => Q) g k
    let W := laggedWindow directions tau0 H
    virtualGradient W H.gradient=CG.gradient Q g k ∧
      windowDirection W (virtualGradient W H.gradient)=CG.direction Q g k ∧
      H.gradient+Q (virtualCorrection W H.gradient)=CG.gradient Q g k := by
  let trial : History (EuclideanSpace ℝ (Fin m)) → ℝ := laggedTrial directions tau0
  let method := xrfcBasisMethod directions trial
  let H := oneGradientRun method (fun _ => Q) g k
  let W := laggedWindow directions tau0 H
  have ht (K : History (EuclideanSpace ℝ (Fin m))) : trial K≠0 :=
    (lagged_trial_positive directions htau0 K).ne'
  have hv : H.displacement+virtualCorrection W H.gradient=CG.displacement Q g k ∧
      virtualGradient W H.gradient=CG.gradient Q g k ∧
      windowDirection W (virtualGradient W H.gradient)=CG.direction Q g k := by
    cases directions with
    | false =>
      have h := xrfc_full_reference trial Q hQ hpos g N hpre (fun _ _ => ht _) k hk
      dsimp only [W]
      rw [lagged_window_step,selectedWindow_full]
      change H.displacement+virtualCorrection (selectedWindow fullMemory H) H.gradient=CG.displacement Q g k ∧
        virtualGradient H.pairs H.gradient=CG.gradient Q g k ∧
        windowDirection H.pairs (virtualGradient H.pairs H.gradient)=CG.direction Q g k at h
      simpa only [selectedWindow_full] using h
    | true =>
      have h := xrfcD_reference fullMemory trial Q hQ hpos g N hpre
        (fun _ _ hi => hi) (fun _ _ => ht _) k hk
      dsimp only [W]
      rw [lagged_window_direction]
      exact h
  refine ⟨hv.2.1,hv.2.2,?_⟩
  calc
    _ = g+Q H.displacement+Q (virtualCorrection W H.gradient) := by
      rw [oneGradientRun_quadratic_gradient]
    _ = g+Q (H.displacement+virtualCorrection W H.gradient) := by rw [map_add];abel
    _ = CG.gradient Q g k := by rw [hv.1,CG.gradient_displacement]

/-- The real lagged policy's next decision equals the genuinely measured
previous CG exact line length in either implemented XRFC basis.
Use: establish the source lagged-trial dictionary from actual observations,
including arbitrary initial overshoot or undershoot.
Article: main_krylov, prop:hb, tau_(k+1)=alpha_k.
Proof: genuine native virtual consistency makes the observed new gradient
difference exactly tau_k Q d_k. Its actual positive previous trial cancels;
the reconstructed line is the true positive CG line, so no fallback is used. -/
theorem lagged_trial_reference_next (directions : Bool) {tau0 : ℝ} (htau0 : 0<tau0)
    (Q : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v,v≠0 → 0 < inner ℝ v (Q v))
    (g : EuclideanSpace ℝ (Fin m)) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (k : ℕ) (hk : k<N) :
    let trial : History (EuclideanSpace ℝ (Fin m)) → ℝ := laggedTrial directions tau0
    let method := xrfcBasisMethod directions trial
    trial (oneGradientRun method (fun _ => Q) g (k+1))=CG.length Q g k := by
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
  have hraw : laggedMeasuredLength W H.gradient (trial H) (H.gradient+Q (method.step H))=CG.length Q g k := by
    change lineLength gv d ((trial H)⁻¹ • (H.gradient+Q (method.step H)-gv))=_
    rw [hprobe,hvg,hd]
  have hpositive := (CG.invariant_line_pos Q hpos g k (CG.invariant Q hQ hpos g k
    (fun i hi => hpre i (hi.trans hk))) (hpre k hk)).2.1
  change laggedTrial directions tau0 (oneGradientAdvance method Q H)=_
  rw [lagged_trial_advance,hraw,ite_eq_left hpositive]

end
end krylov.OneGradient
