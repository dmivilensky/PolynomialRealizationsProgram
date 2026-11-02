import krylov.Methods.NazarethReference
import krylov.Methods.EvaluatedGeometry
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical and prop:launch, actual Nazareth launch bridge.
Use: connect the literal measured three-term executor to the real evaluated
projection transcript through an explicitly computed data-only trial rescaling.
Source: actual positive CG direction factors, true predicted observed solves
and genuine one-gradient history induction; no output or trajectory equality is assumed. -/

namespace krylov.Methods
noncomputable section
open krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The effective CG-normalized evaluated length of the actual Nazareth
step, computed solely from the original measured history and supplied trial.
Use: this derives an implementation bridge without changing the original
Nazareth trial schedule or supplying a reference CG direction to the policy.
Article: main_krylov, prop:classical(a) and prop:launch(a). -/
def nazarethEvaluatedTrial (trial : History E → ℝ) (H : History E) : ℝ :=
  let d := windowDirection H.pairs (virtualGradient H.pairs H.gradient)
  trial H*inner ℝ d (nazarethDirection trial H)/‖d‖^2

/-- The actual observed normalization reads exactly the real positive CG
scale of the genuine Nazareth direction and selects a positive effective length.
Use: all nonzero-trial domains of the evaluated-launch executor are derived.
Article: main_krylov, prop:classical(a).
Proof: native Nazareth execution derives its positive CG direction factor and
the true predicted direction. Its nonzero squared norm cancels in the actual
observed scalar quotient, leaving the original trial times that real factor. -/
theorem nazareth_evaluated_trial_reference (trial : History E → ℝ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,0 < trial (oneGradientRun (nazarethMethod trial) (fun _ => Q) g i))
    (k : ℕ) (hk : k<N) :
    let H := oneGradientRun (nazarethMethod trial) (fun _ => Q) g k
    ∃ scale : ℝ,0<scale ∧ nazarethDirection trial H=scale • CG.direction Q g k ∧
      nazarethEvaluatedTrial trial H=trial H*scale ∧ 0<nazarethEvaluatedTrial trial H := by
  let H := oneGradientRun (nazarethMethod trial) (fun _ => Q) g k
  obtain ⟨scale,hscale,hdir⟩ := nazareth_direction_reference trial Q hQ hpos g N hpre ht k hk
  have hv := (nazareth_predicted_reference trial Q hQ hpos g N hpre ht k hk.le).2.2
  have hd := (CG.invariant_line_pos Q hpos g k
    (CG.invariant Q hQ hpos g k (fun i hi => hpre i (hi.trans hk))) (hpre k hk)).1
  have hn : ‖CG.direction Q g k‖^2≠0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hd)
  have he : nazarethEvaluatedTrial trial H=trial H*scale := by
    unfold nazarethEvaluatedTrial
    dsimp only
    rw [hv,hdir,real_inner_smul_right,real_inner_self_eq_norm_sq]
    field_simp
  exact ⟨scale,hscale,hdir,he,he ▸ mul_pos (ht k hk) hscale⟩

/-- The literal original Nazareth method and the genuine evaluated-launch
projection method have exactly the same complete actual quadratic histories,
with the explicitly observed effective trial, through every active prefix.
Use: original evaluated-launch geometry applies to the named implementation;
this is an executed equality of all observations, not a prescribed trajectory.
Article: main_krylov, prop:classical(a,b) and prop:launch(a).
Proof: at the actual native history, the true predicted direction is CG and
the observed effective length is its original trial times the real positive
Nazareth direction factor. Both methods therefore issue the identical actual
query; genuine one-gradient updates preserve the full history inductively. -/
theorem nazareth_evaluated_histories (trial : History E → ℝ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,0 < trial (oneGradientRun (nazarethMethod trial) (fun _ => Q) g i))
    (k : ℕ) (hk : k≤N) :
    oneGradientRun (evaluatedLaunchMethod (nazarethEvaluatedTrial trial)) (fun _ => Q) g k=
      oneGradientRun (nazarethMethod trial) (fun _ => Q) g k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    let H := oneGradientRun (nazarethMethod trial) (fun _ => Q) g k
    have hv := (nazareth_predicted_reference trial Q hQ hpos g N hpre ht k (by omega)).2.2
    obtain ⟨scale,_,hdir,he,_⟩ := nazareth_evaluated_trial_reference trial Q hQ hpos g N hpre ht k (by omega)
    have hs : (evaluatedLaunchMethod (nazarethEvaluatedTrial trial)).step H=(nazarethMethod trial).step H := by
      change nazarethEvaluatedTrial trial H • windowDirection H.pairs (virtualGradient H.pairs H.gradient)=
        trial H • nazarethDirection trial H
      rw [he,hv,hdir,smul_smul]
    change oneGradientAdvance (evaluatedLaunchMethod (nazarethEvaluatedTrial trial)) Q
      (oneGradientRun (evaluatedLaunchMethod (nazarethEvaluatedTrial trial)) (fun _ => Q) g k)=
      oneGradientAdvance (nazarethMethod trial) Q H
    rw [ih (by omega)]
    change History.mk H.initial (⟨0,0,_,H.gradient+Q _,[]⟩::H.records)=
      History.mk H.initial (⟨0,0,_,H.gradient+Q _,[]⟩::H.records)
    rw [hs]

/-- The actual effective evaluated-launch trials are positive on their own
true complete histories for the genuine original Nazareth positive schedule.
Use: every original evaluated-launch geometry and support theorem receives
its genuine nonzero-trial hypothesis on the actual comparison executor.
Article: main_krylov, prop:classical and prop:launch(a).
Proof: the complete actual histories coincide with native Nazareth histories,
where the observed effective trial has already been proved strictly positive. -/
theorem nazareth_evaluated_trials_positive (trial : History E → ℝ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,0 < trial (oneGradientRun (nazarethMethod trial) (fun _ => Q) g i)) :
    ∀ k<N,0<nazarethEvaluatedTrial trial
      (oneGradientRun (evaluatedLaunchMethod (nazarethEvaluatedTrial trial)) (fun _ => Q) g k) := by
  intro k hk
  rw [nazareth_evaluated_histories trial Q hQ hpos g N hpre ht k hk.le]
  obtain ⟨_,_,_,_,hp⟩ := nazareth_evaluated_trial_reference trial Q hQ hpos g N hpre ht k hk
  exact hp

end
end krylov.Methods
