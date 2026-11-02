import krylov.Methods.NazarethEvaluated
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical(a,b), literal Nazareth trial errors.
Use: express the actual measured evaluated steps and complete trajectory in
the original relative trial errors from the actual evaluated point.
Source: genuine observed Nazareth/evaluated history bridge, positive CG
scaling and true rescaling covariance of the actual exact line length. -/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Reference
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The original Nazareth relative trial error measured from its actual
evaluated point along its literal computed direction.
Use: source epsilon uses the real queried trial, rather than an effective
CG normalization or a prescribed reference sequence.
Article: main_krylov, prop:classical(a). -/
def nazarethTrialError (trial : History E → ℝ) (Q : E →L[ℝ] E) (g : E) (k : ℕ) : ℝ :=
  let H := oneGradientRun (nazarethMethod trial) (fun _ => Q) g k
  let d := nazarethDirection trial H
  1-trial H/lineLength H.gradient d (Q d)

/-- The actual exact length from a native Nazareth evaluated point is the
true CG length divided by its genuinely computed positive direction scale.
Use: measured native trial errors have exactly the source line-search meaning.
Article: main_krylov, prop:classical(a).
Proof: actual complete histories equal the real evaluated projection histories,
whose exact CG-direction line length is proved from actual conjugacy. The
genuine direction-scaling identity gives the literal Nazareth line length. -/
theorem nazareth_exact_evaluated_length (trial : History E → ℝ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,0 < trial (oneGradientRun (nazarethMethod trial) (fun _ => Q) g i))
    (k : ℕ) (hk : k<N) :
    let H := oneGradientRun (nazarethMethod trial) (fun _ => Q) g k
    ∃ scale : ℝ,0<scale ∧ nazarethDirection trial H=scale • CG.direction Q g k ∧
      lineLength H.gradient (nazarethDirection trial H) (Q (nazarethDirection trial H))=CG.length Q g k/scale := by
  let H := oneGradientRun (nazarethMethod trial) (fun _ => Q) g k
  obtain ⟨scale,hscale,hdir⟩ := nazareth_direction_reference trial Q hQ hpos g N hpre ht k hk
  have hline := evaluated_launch_exact_length (nazarethEvaluatedTrial trial) Q hQ hpos g N hpre
    (fun j hj => (nazareth_evaluated_trials_positive trial Q hQ hpos g N hpre ht j hj).ne') k hk.le
  rw [nazareth_evaluated_histories trial Q hQ hpos g N hpre ht k hk.le] at hline
  refine ⟨scale,hscale,hdir,?_⟩
  rw [hdir,map_smul,lineLength_smul _ _ _ hscale.ne',hline]

/-- The literal original Nazareth measured step is exactly the true CG step
multiplied by one minus its actual evaluated-point relative trial error.
Use: this proves the source classical step comparison for the real algorithm
and its original supplied trial lengths, with no trial reparameterization.
Article: main_krylov, prop:classical(a), s_j=(one-epsilon_j)*alpha_j*d_j.
Proof: genuine computed positive direction scaling and the actual exact line
length identify the original error. Cancel only the true nonzero CG length
and scale, then substitute into the real measured step. -/
theorem nazareth_step_trial_error (trial : History E → ℝ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,0 < trial (oneGradientRun (nazarethMethod trial) (fun _ => Q) g i))
    (k : ℕ) (hk : k<N) :
    oneGradientStep (nazarethMethod trial) (fun _ => Q) g k=
      ((1-nazarethTrialError trial Q g k)*CG.length Q g k) • CG.direction Q g k := by
  let H := oneGradientRun (nazarethMethod trial) (fun _ => Q) g k
  obtain ⟨scale,hscale,hdir,hline⟩ := nazareth_exact_evaluated_length trial Q hQ hpos g N hpre ht k hk
  have ha := (CG.invariant_line_pos Q hpos g k
    (CG.invariant Q hQ hpos g k (fun i hi => hpre i (hi.trans hk))) (hpre k hk)).2.1
  have he : (1-nazarethTrialError trial Q g k)*CG.length Q g k=trial H*scale := by
    change (1-(1-trial H/lineLength H.gradient (nazarethDirection trial H)
      (Q (nazarethDirection trial H))))*CG.length Q g k=_
    rw [hline]
    field_simp
    ring
  change trial H • nazarethDirection trial H=_
  rw [he,hdir,smul_smul]

/-- Every native evaluated Nazareth point retains the full accumulated sum
of all its original actual relative trial misses from the true CG point.
Use: the original evaluated-launch error differs from XRFC's newest-only miss
for the literal named classical algorithm and its real measured history.
Article: main_krylov, prop:classical(a).
Proof: sum the actual measured steps, insert their proved original trial-error
formula and subtract the true CG displacement sum coefficient by coefficient. -/
theorem nazareth_evaluated_displacement (trial : History E → ℝ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,0 < trial (oneGradientRun (nazarethMethod trial) (fun _ => Q) g i))
    (k : ℕ) (hk : k≤N) :
    (oneGradientRun (nazarethMethod trial) (fun _ => Q) g k).displacement=CG.displacement Q g k-
      ∑ i∈Finset.range k,(nazarethTrialError trial Q g i*CG.length Q g i) • CG.direction Q g i := by
  rw [oneGradientRun_displacement_sum,CG.displacement,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [nazareth_step_trial_error trial Q hQ hpos g N hpre ht i (by have := Finset.mem_range.mp hi;omega),← sub_smul]
  congr 1
  ring

/-- The actual original Nazareth latest-information model is precisely the
true diagonal matrix of measured physical pair energies.
Use: source diagonal coefficients concern the literal named implementation.
Article: main_krylov, prop:classical(b).
Proof: the genuine complete histories coincide with the evaluated projection
executor at its proved positive observed effective lengths; transfer its
actual conjugate-pair diagonal model identity. -/
theorem nazareth_model_diagonal (trial : History E → ℝ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,0 < trial (oneGradientRun (nazarethMethod trial) (fun _ => Q) g i))
    (k : ℕ) (hk : k≤N) :
    let H := oneGradientRun (nazarethMethod trial) (fun _ => Q) g k
    windowModel H.pairs=diagonal (fun i => inner ℝ (windowSteps H.pairs i) (windowImages H.pairs i)) := by
  have he := nazareth_evaluated_histories trial Q hQ hpos g N hpre ht k hk
  dsimp only
  rw [← he]
  exact evaluated_launch_model_diagonal (nazarethEvaluatedTrial trial) Q hQ hpos g N hpre
    (fun j hj => (nazareth_evaluated_trials_positive trial Q hQ hpos g N hpre ht j hj).ne') k hk

end
end krylov.Methods
