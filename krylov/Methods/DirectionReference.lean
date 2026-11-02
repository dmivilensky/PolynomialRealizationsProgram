import krylov.Methods.DirectionExecution
import krylov.Methods.XRFCDTermination
set_option autoImplicit false
/-!
Article: main_krylov, thm:I and lem:U(d), true direction-replay reference domains.
Use: derive the actual direction/image arrays and both native finite solve
domains from the original executed quadratic XRFC-D consistency theorem.
Source: reused actual data-only replay correctness, CG virtual consistency
and true positive retained quadratic model, including the terminal output.
-/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual original full-memory XRFC-D direction is the genuine CG direction.
Use: the reference array is derived from actual execution rather than postulated.
Article: main_krylov, thm:I, direction-basis reference.
Proof: the existing real positive-window consistency theorem applies to full
memory and identifies the actual computed virtual direction at every true prefix. -/
theorem xrfcD_executed_direction_reference (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => Q) g i)≠0)
    (k : ℕ) (hk : k≤N) :
    xrfcDExecutedDirection trial (fun _ => Q) g k=CG.direction Q g k :=
  (xrfcD_reference fullMemory trial Q hQ hpos g N hpre (fun _ _ hi => hi) ht k hk).2.2

/-- Every actual returned-gradient replay image is the true reference operator
image of its actual CG direction on quadratic data.
Use: derive the real direction-basis inverse domains from genuine observed pairs.
Article: main_krylov, thm:I and lem:U(d).
Proof: compare the newest pair of the exact actual execution transcript with
the existing proved quadratic data-only replay transcript. -/
theorem xrfcD_executed_image_reference (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => Q) g i)≠0)
    (k : ℕ) (hk : k<N) :
    xrfcDExecutedImage trial (fun _ => Q) g k=Q (CG.direction Q g k) := by
  have h := (xrfcD_state fullMemory trial Q hQ hpos g N hpre
    (fun _ _ hi => hi) ht (k+1) (by omega)).1
  rw [xrfcD_run_replay] at h
  change (xrfcDExecutedDirection trial (fun _ => Q) g k,xrfcDExecutedImage trial (fun _ => Q) g k)::_=
    (CG.direction Q g k,Q (CG.direction Q g k))::_ at h
  exact congrArg Prod.snd (List.cons.inj h).1

/-- The real full-memory XRFC-D model and conjugacy array determinants are
nonzero on every genuine quadratic reference prefix, including the final solve.
Use: actual C-r regularity has no supplied inverse-domain assumptions.
Article: main_krylov, lem:U(d) and thm:I.
Proof: the actual replay equals the positive retained quadratic direction
window. Its actual positive model is the true operator Gram matrix; the
existing executed determinant reindexing transfers it to the real fixed arrays.
True quadratic replay images then identify the native pair model as the same Gram. -/
theorem xrfcD_full_array_domains (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => Q) g i)≠0)
    (k : ℕ) (hk : k≤N) :
    let D := fun i : Fin k => xrfcDExecutedDirection trial (fun _ => Q) g (k-1-i.val)
    let Y := fun i : Fin k => xrfcDExecutedImage trial (fun _ => Q) g (k-1-i.val)
    (crossGram Y D).det≠0 ∧ (pairModel D Y).det≠0 := by
  let W := xrfcDWindow trial (fun _ => Q) g k
  have hW : W=directionWindow Q g k k := by
    unfold W xrfcDWindow selectedDirectionWindow
    rw [(xrfcD_state fullMemory trial Q hQ hpos g N hpre
      (fun _ _ hi => hi) ht k hk).1,oneGradientRun_length]
    rfl
  have hy : ∀ i : Fin W.length,windowImages W i=Q (windowSteps W i) := by
    rw [hW]
    exact directionWindow_images Q g k k
  have hp : (windowModel W).det≠0 :=
    (xrfcD_model_posDef fullMemory trial Q hQ hpos g N hpre (fun _ _ hi => hi) ht k hk).det_pos.ne'
  rw [windowModel_quadratic W Q hQ hy] at hp
  have hYw : windowImages W=fun i => Q (windowSteps W i) := funext hy
  rw [← hYw] at hp
  change (crossGram (windowImages (xrfcDWindow trial (fun _ => Q) g k))
    (windowSteps (xrfcDWindow trial (fun _ => Q) g k))).det≠0 at hp
  rw [xrfcD_full_window,crossGram_executed_det] at hp
  let D := fun i : Fin k => xrfcDExecutedDirection trial (fun _ => Q) g (k-1-i.val)
  let Y := fun i : Fin k => xrfcDExecutedImage trial (fun _ => Q) g (k-1-i.val)
  have hY : Y=fun i => Q (D i) := by
    funext i
    dsimp only [Y,D]
    rw [xrfcD_executed_image_reference trial Q hQ hpos g N hpre ht _ (by omega),
      xrfcD_executed_direction_reference trial Q hQ hpos g N hpre ht _ (by omega)]
  have hm : pairModel D Y=crossGram Y D := by
    rw [hY,pairModel_quadratic D Q hQ]
    ext i j
    exact (hQ (D i) (D j)).symm
  exact ⟨hp,by rw [hm];exact hp⟩

end
end krylov.Methods
