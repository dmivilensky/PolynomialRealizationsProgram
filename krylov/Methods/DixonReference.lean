import krylov.Methods.DixonObserved
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical, actual predicted-gradient Dixon directions.
Use: identify the literal observed Fletcher--Reeves and identity-initialized
BFGS directions on the genuine evaluated transcript, then derive execution equality.
Source: actual own-returned-gradient predictor, genuine conjugate observed
BFGS action and the original real CG gradient/direction recurrences. -/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual previous direction reconstructed on the true evaluated
projection transcript is precisely the genuine preceding CG direction.
Use: the literal predicted-gradient Dixon recurrence receives its own real
previous computed direction, without a reference direction argument.
Article: main_krylov, prop:classical(a), Dixon75 Section 3.
Proof: actual queried steps are the actual old trial times the true current
CG direction. Recover the real preceding history and cancel its nonzero trial. -/
theorem evaluated_measured_trial_direction (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ j<N,CG.gradient Q g j≠0)
    (ht : ∀ j<N,trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g j)≠0)
    (k : ℕ) (hk : k<N) :
    measuredTrialDirection trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g (k+1))=
      CG.direction Q g k := by
  let method := evaluatedLaunchMethod trial
  change (trial (historyTail (oneGradientRun method (fun _ => Q) g (k+1))))⁻¹ •
    method.step (oneGradientRun method (fun _ => Q) g k)=_
  rw [oneGradient_historyTail_succ,evaluated_launch_step trial Q hQ hpos g N hpre ht k hk.le,
    smul_smul,inv_mul_cancel₀ (ht k hk),one_smul]

/-- The literal predicted-gradient Fletcher--Reeves direction is exactly
CG on the real evaluated-launch transcript, for arbitrary nonzero trials.
Use: Dixon's direction comparison is derived from its actual observed formula.
Article: main_krylov, prop:classical(a), Dixon75 Section 3.
Proof: the actual recorded gradient projection gives the genuine CG gradient
at the current and preceding history. True measured direction reconstruction
and the actual CG recurrence identify the literal Fletcher--Reeves formula. -/
theorem dixon_fr_evaluated_direction (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ j<N,CG.gradient Q g j≠0)
    (ht : ∀ j<N,trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g j)≠0)
    (k : ℕ) (hk : k≤N) :
    dixonFRDirection trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g k)=CG.direction Q g k := by
  cases k with
  | zero =>
    change -(g+0)+(‖g+0‖^2/‖g+0‖^2) • (0 : E)= -g
    rw [smul_zero,add_zero,add_zero]
  | succ k =>
    unfold dixonFRDirection
    rw [oneGradient_historyTail_succ,
      evaluated_recorded_predicted_gradient trial Q hQ hpos g N hpre ht (k+1) hk,
      evaluated_recorded_predicted_gradient trial Q hQ hpos g N hpre ht k (by omega),
      evaluated_measured_trial_direction trial Q hQ hpos g N hpre ht k (by omega)]
    rfl

/-- The genuine identity-initialized BFGS action on the literal recorded
predicted gradient is exactly the current CG direction on real observations.
Use: the named Dixon quasi-Newton implementation uses the actual accumulated
two-loop inverse model on its own genuine pairs, not a supplied CG direction.
Article: main_krylov, prop:classical(a), Dixon73 with BFGS and H0=I.
Proof: actual conjugate observed pairs have positive energies. Their true
predicted gradient is orthogonal to every old step. Reuse the genuine BFGS
conjugate-pair identity and the actual native predicted-direction theorem. -/
theorem dixon_bfgs_evaluated_direction (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ j<N,CG.gradient Q g j≠0)
    (ht : ∀ j<N,trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g j)≠0)
    (k : ℕ) (hk : k≤N) :
    let H := oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g k
    show Prop from -inverseBFGSApply 1 H.pairs (recordedPredictedGradient H)=CG.direction Q g k := by
  let H := oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g k
  have hb := evaluated_launch_basis trial Q hQ hpos g N hpre ht k hk
  have hv := evaluated_launch_reference trial Q hQ hpos g N hpre ht k hk
  have hy (i : Fin H.pairs.length) : windowImages H.pairs i=Q (windowSteps H.pairs i) :=
    oneGradientRun_pairs_quadratic _ _ _ _ (H.pairs.get i) (List.get_mem _ i)
  have hg : ∀ i,inner ℝ (windowSteps H.pairs i) (CG.gradient Q g k)=0 := by
    intro i
    apply directionFlag_gradient_orthogonal Q hQ hpos g k (fun j hj => hpre j (hj.trans_le hk))
    rw [← hb.2]
    exact Submodule.subset_span ⟨i,rfl⟩
  have hd : ∀ i,inner ℝ (windowSteps H.pairs i) (windowImages H.pairs i)≠0 := by
    intro i
    rw [hy]
    exact (hpos _ (hb.1.ne_zero i)).ne'
  have hG : crossGram (windowImages H.pairs) (windowSteps H.pairs)=windowModel H.pairs := by
    rw [show windowImages H.pairs=(fun i => Q (windowSteps H.pairs i)) from funext hy,
      windowModel_quadratic H.pairs Q hQ hy]
  have hoff (i j : Fin H.pairs.length) (hij : i≠j) :
      inner ℝ (windowImages H.pairs i) (windowSteps H.pairs j)=0 := by
    have he := congrFun (congrFun hG i) j
    rw [evaluated_launch_model_diagonal trial Q hQ hpos g N hpre ht k hk,
      Matrix.diagonal_apply_ne _ hij] at he
    exact he
  have hp := evaluated_recorded_predicted_gradient trial Q hQ hpos g N hpre ht k hk
  change recordedPredictedGradient H=CG.gradient Q g k at hp
  change -inverseBFGSApply 1 H.pairs (recordedPredictedGradient H)=_
  rw [hp,inverseBFGSApply_eq_conjugacy 1 H.pairs (CG.gradient Q g k) hg hd hoff,one_smul,← hv.2.1,hv.2.2]

/-- Equal genuinely executed step decisions preserve every actual observed
one-gradient history, independently of both methods' unevaluated outputs.
Use: implementation bridges are proved by real query induction.
Article: main_krylov, prop:classical.
Proof: each method makes the same actual query at the first executor's
history; identical returned segment actions extend the same complete history. -/
theorem oneGradient_histories_of_steps (first second : OneGradientMethod E)
    (A : ℕ → E →L[ℝ] E) (g : E) (N : ℕ)
    (hs : ∀ k<N,first.step (oneGradientRun first A g k)=second.step (oneGradientRun first A g k))
    (k : ℕ) (hk : k≤N) : oneGradientRun first A g k=oneGradientRun second A g k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change oneGradientAdvance first (A k) (oneGradientRun first A g k)=
      oneGradientAdvance second (A k) (oneGradientRun second A g k)
    rw [← ih (by omega)]
    unfold oneGradientAdvance
    rw [hs k (by omega)]

/-- Both literal predicted-gradient Dixon implementations have exactly the
actual evaluated-launch complete transcript for every actually positive original trial prefix.
Use: the named classical trajectory and correction comparisons follow on the
real implemented CG/BFGS methods, with no supplied CG-consistency field.
Article: main_krylov, prop:classical(a,b), Dixon73/Dixon75.
Proof: real recorded predictors and genuine two-loop BFGS action give exactly
the current CG direction at every true evaluated transcript. Their actual
measured queries coincide, and strong actual query induction first derives the comparison trial domains
from earlier true history equalities, so global off-history positivity is unnecessary. -/
theorem dixon_evaluated_histories (bfgs : Bool) (trial : History E → ℝ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (N : ℕ) (hpre : ∀ j<N,CG.gradient Q g j≠0)
    (ht : ∀ j<N,0 < trial (oneGradientRun
      (if bfgs then dixonBFGSMethod trial else dixonCGMethod trial) (fun _ => Q) g j))
    (k : ℕ) (hk : k≤N) :
    let method := if bfgs then dixonBFGSMethod trial else dixonCGMethod trial
    oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g k=oneGradientRun method (fun _ => Q) g k := by
  let method := if bfgs then dixonBFGSMethod trial else dixonCGMethod trial
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => rfl
    | succ j =>
      have hprev := ih j (by omega) (by omega)
      have hT : ∀ i<j+1,trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g i)≠0 := by
        intro i hi
        rw [ih i hi (by omega)]
        exact (ht i (by omega)).ne'
      have hpre' : ∀ i<j+1,CG.gradient Q g i≠0 := fun i hi => hpre i (by omega)
      have hv := (evaluated_launch_reference trial Q hQ hpos g (j+1) hpre' hT j (by omega)).2.2
      have hs : (evaluatedLaunchMethod trial).step
          (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g j)=
          method.step (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g j) := by
        cases bfgs with
        | false =>
          change trial _ • windowDirection _ (virtualGradient _ _)=trial _ • dixonFRDirection trial _
          rw [hv,dixon_fr_evaluated_direction trial Q hQ hpos g (j+1) hpre' hT j (by omega)]
        | true =>
          change trial _ • windowDirection _ (virtualGradient _ _)=
            trial _ • (-inverseBFGSApply 1 _ (recordedPredictedGradient _))
          rw [hv,dixon_bfgs_evaluated_direction trial Q hQ hpos g (j+1) hpre' hT j (by omega)]
      change oneGradientAdvance (evaluatedLaunchMethod trial) Q
        (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g j)=
        oneGradientAdvance method Q (oneGradientRun method (fun _ => Q) g j)
      rw [← hprev]
      unfold oneGradientAdvance
      rw [hs]

end
end krylov.Methods
