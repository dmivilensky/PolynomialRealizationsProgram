import krylov.Methods.DixonReference
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical(a,b), original Dixon evaluated trial errors.
Use: prove the named CG/BFGS methods' actual evaluated-point exact length,
measured trial-error steps, full missed-line trajectory and diagonal model.
Source: real observed direction and complete implementation-history identities;
positivity is needed only along the actual original executed prefix. -/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Reference
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The literal computed search direction of the selected original Dixon
predicted-gradient implementation, with identity initial BFGS metric.
Use: the original relative error is measured along the real computed direction.
Article: main_krylov, prop:classical(a). -/
def dixonSearchDirection (bfgs : Bool) (trial : History E → ℝ) (H : History E) : E :=
  if bfgs then -inverseBFGSApply 1 H.pairs (recordedPredictedGradient H) else dixonFRDirection trial H

/-- The original relative trial error along the selected actual Dixon search
direction from its true evaluated point.
Use: no effective reference length is substituted in this data definition.
Article: main_krylov, prop:classical(a). -/
def dixonTrialError (bfgs : Bool) (trial : History E → ℝ) (Q : E →L[ℝ] E) (g : E) (k : ℕ) : ℝ :=
  let method := if bfgs then dixonBFGSMethod trial else dixonCGMethod trial
  let H := oneGradientRun method (fun _ => Q) g k
  let d := dixonSearchDirection bfgs trial H
  1-trial H/lineLength H.gradient d (Q d)

/-- Both literal original Dixon computed directions are exactly the true
CG direction on their own genuine active quadratic transcript.
Use: the named reference implementation bridge has no direction or output
correctness premise, and positivity is only on actually selected trials.
Article: main_krylov, prop:classical(a), Dixon73/Dixon75.
Proof: the proved actual complete histories identify the comparison transcript;
the actual recorded Fletcher--Reeves/BFGS direction formulas there are CG. -/
theorem dixon_direction_reference (bfgs : Bool) (trial : History E → ℝ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (N : ℕ) (hpre : ∀ j<N,CG.gradient Q g j≠0)
    (ht : ∀ j<N,0 < trial (oneGradientRun
      (if bfgs then dixonBFGSMethod trial else dixonCGMethod trial) (fun _ => Q) g j))
    (k : ℕ) (hk : k≤N) :
    dixonSearchDirection bfgs trial (oneGradientRun
      (if bfgs then dixonBFGSMethod trial else dixonCGMethod trial) (fun _ => Q) g k)=CG.direction Q g k := by
  have he := dixon_evaluated_histories bfgs trial Q hQ hpos g N hpre ht k hk
  have hT : ∀ j<N,trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g j)≠0 := by
    intro j hj
    rw [dixon_evaluated_histories bfgs trial Q hQ hpos g N hpre ht j hj.le]
    exact (ht j hj).ne'
  rw [← he]
  cases bfgs with
  | false => exact dixon_fr_evaluated_direction trial Q hQ hpos g N hpre hT k hk
  | true => exact dixon_bfgs_evaluated_direction trial Q hQ hpos g N hpre hT k hk

/-- The exact line from each literal original Dixon evaluated point along
its actual computed direction is the true current CG length.
Use: original measured errors are relative to the actual evaluated-point line.
Article: main_krylov, prop:classical(a).
Proof: actual directions are proved CG and real complete histories coincide
with the genuine evaluated projection executor, whose exact length follows
from actual stored-step conjugacy and its real predicted point. -/
theorem dixon_exact_evaluated_length (bfgs : Bool) (trial : History E → ℝ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (N : ℕ) (hpre : ∀ j<N,CG.gradient Q g j≠0)
    (ht : ∀ j<N,0 < trial (oneGradientRun
      (if bfgs then dixonBFGSMethod trial else dixonCGMethod trial) (fun _ => Q) g j))
    (k : ℕ) (hk : k≤N) :
    let method := if bfgs then dixonBFGSMethod trial else dixonCGMethod trial
    let H := oneGradientRun method (fun _ => Q) g k
    lineLength H.gradient (dixonSearchDirection bfgs trial H) (Q (dixonSearchDirection bfgs trial H))=CG.length Q g k := by
  have he := dixon_evaluated_histories bfgs trial Q hQ hpos g N hpre ht k hk
  have hT : ∀ j<N,trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g j)≠0 := by
    intro j hj
    rw [dixon_evaluated_histories bfgs trial Q hQ hpos g N hpre ht j hj.le]
    exact (ht j hj).ne'
  dsimp only
  rw [dixon_direction_reference bfgs trial Q hQ hpos g N hpre ht k hk,← he]
  exact evaluated_launch_exact_length trial Q hQ hpos g N hpre hT k hk

/-- Both literal original Dixon measured steps have exactly the source
one-minus-relative-error CG step form, using their real evaluated-point error.
Use: the comparison concerns the original actual trial schedule and direction.
Article: main_krylov, prop:classical(a).
Proof: the actual exact evaluated length is the genuine positive CG length.
Cancel that true denominator in the literal relative error and insert the
proved real computed direction into the actual trial step. -/
theorem dixon_step_trial_error (bfgs : Bool) (trial : History E → ℝ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (N : ℕ) (hpre : ∀ j<N,CG.gradient Q g j≠0)
    (ht : ∀ j<N,0 < trial (oneGradientRun
      (if bfgs then dixonBFGSMethod trial else dixonCGMethod trial) (fun _ => Q) g j))
    (k : ℕ) (hk : k<N) :
    let method := if bfgs then dixonBFGSMethod trial else dixonCGMethod trial
    oneGradientStep method (fun _ => Q) g k=
      ((1-dixonTrialError bfgs trial Q g k)*CG.length Q g k) • CG.direction Q g k := by
  let method := if bfgs then dixonBFGSMethod trial else dixonCGMethod trial
  let H := oneGradientRun method (fun _ => Q) g k
  have hline := dixon_exact_evaluated_length bfgs trial Q hQ hpos g N hpre ht k hk.le
  have hdir := dixon_direction_reference bfgs trial Q hQ hpos g N hpre ht k hk.le
  have ha := (CG.invariant_line_pos Q hpos g k
    (CG.invariant Q hQ hpos g k (fun i hi => hpre i (hi.trans hk))) (hpre k hk)).2.1
  have hcoef : (1-dixonTrialError bfgs trial Q g k)*CG.length Q g k=trial H := by
    change (1-(1-trial H/lineLength H.gradient (dixonSearchDirection bfgs trial H)
      (Q (dixonSearchDirection bfgs trial H))))*CG.length Q g k=_
    rw [hline]
    field_simp
    ring
  have hs : method.step H=trial H • dixonSearchDirection bfgs trial H := by cases bfgs <;> rfl
  change method.step H=_
  rw [hs,hdir,hcoef]

/-- Every literal original Dixon evaluated point retains the full sum of
all actual relative trial misses from the true CG point.
Use: both named algorithms have the printed evaluated-launch trajectory
for their original supplied positive trial schedule.
Article: main_krylov, prop:classical(a).
Proof: sum actual recorded queries, insert the proved original trial-error
step identity and compare coefficient by coefficient with the genuine CG sum. -/
theorem dixon_evaluated_displacement (bfgs : Bool) (trial : History E → ℝ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (N : ℕ) (hpre : ∀ j<N,CG.gradient Q g j≠0)
    (ht : ∀ j<N,0 < trial (oneGradientRun
      (if bfgs then dixonBFGSMethod trial else dixonCGMethod trial) (fun _ => Q) g j))
    (k : ℕ) (hk : k≤N) :
    let method := if bfgs then dixonBFGSMethod trial else dixonCGMethod trial
    (oneGradientRun method (fun _ => Q) g k).displacement=CG.displacement Q g k-
      ∑ i∈Finset.range k,(dixonTrialError bfgs trial Q g i*CG.length Q g i) • CG.direction Q g i := by
  dsimp only
  rw [oneGradientRun_displacement_sum,CG.displacement,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [dixon_step_trial_error bfgs trial Q hQ hpos g N hpre ht i (by have := Finset.mem_range.mp hi;omega),← sub_smul]
  congr 1
  ring

/-- Both original Dixon observed latest models are exactly the true
diagonal measured pair-energy matrices on their actual quadratic transcripts.
Use: the source predicted-point coefficient formula reads genuine physical pairs.
Article: main_krylov, prop:classical(b).
Proof: genuine complete history equality transfers the actual positive
conjugate-pair diagonal model from the real evaluated projection executor. -/
theorem dixon_model_diagonal (bfgs : Bool) (trial : History E → ℝ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (N : ℕ) (hpre : ∀ j<N,CG.gradient Q g j≠0)
    (ht : ∀ j<N,0 < trial (oneGradientRun
      (if bfgs then dixonBFGSMethod trial else dixonCGMethod trial) (fun _ => Q) g j))
    (k : ℕ) (hk : k≤N) :
    let method := if bfgs then dixonBFGSMethod trial else dixonCGMethod trial
    let H := oneGradientRun method (fun _ => Q) g k
    windowModel H.pairs=diagonal (fun i => inner ℝ (windowSteps H.pairs i) (windowImages H.pairs i)) := by
  have he := dixon_evaluated_histories bfgs trial Q hQ hpos g N hpre ht k hk
  have hT : ∀ j<N,trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g j)≠0 := by
    intro j hj
    rw [dixon_evaluated_histories bfgs trial Q hQ hpos g N hpre ht j hj.le]
    exact (ht j hj).ne'
  dsimp only
  rw [← he]
  exact evaluated_launch_model_diagonal trial Q hQ hpos g N hpre hT k hk

end
end krylov.Methods
