import krylov.Methods.ShortWindow
import krylov.Methods.DirectionWindows

/-!
Article: main_krylov, apA:prop:short, actual prefix before first deletion.
Use: compare real short- and full-memory XRFC histories and identify every
actual recorded step before the first deletion from proved virtual solves.
Source: nonanticipating execution and the actual full-memory XRFC theorem.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Any actual XRFC retention rule agrees with full memory until its first deletion.
Use: short-window counterexamples refer to the real implemented trajectory and its real observations.
Article: main_krylov, apA:prop:short, until the first deletion.
Proof: actual histories agree by induction; each available prefix is fully
retained by both policies, so their data-only steps and next actual query records agree. -/
theorem xrfc_retaining_prefix (memory : ℕ → ℕ) (trial : History E → ℝ)
    (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) (hm : ∀ i<k, i≤memory i) :
    oneGradientRun (xrfcMethod memory trial) A g k=oneGradientRun (xrfcMethod fullMemory trial) A g k := by
  -- Equality concerns the complete real observed history, including every actual recorded step.
  induction k with
  | zero => rfl
  | succ k ih =>
    have he := ih (fun i hi => hm i (by omega))
    let H := oneGradientRun (xrfcMethod fullMemory trial) A g k
    have hl : H.pairs.length≤memory H.records.length := by
      rw [History.pairs_length,oneGradientRun_length]
      exact hm k (by omega)
    have hW : selectedWindow memory H=H.pairs := List.take_of_length_le hl
    change oneGradientAdvance _ _ (oneGradientRun _ A g k)=_
    rw [he]
    change oneGradientAdvance (xrfcMethod memory trial) (A k) H=oneGradientAdvance (xrfcMethod fullMemory trial) (A k) H
    simp only [oneGradientAdvance,xrfcMethod,hW,selectedWindow_full]

/-- Actual fixed-length sliding XRFC has the full-memory observed history through its first deletion time.
Use: all initial bidiagonal steps and the first uncorrected point are those of the real full-memory run.
Article: main_krylov, apA:prop:short, window of m pairs.
Proof: every decision before m+1 has at most m previously recorded pairs. -/
theorem xrfc_sliding_prefix (m : ℕ) (trial : History E → ℝ) (A : ℕ → E →L[ℝ] E) (g : E)
    (k : ℕ) (hk : k≤m+1) :
    oneGradientRun (xrfcMethod (slidingMemory m) trial) A g k=
      oneGradientRun (xrfcMethod fullMemory trial) A g k :=
  xrfc_retaining_prefix _ trial A g k (fun i hi => by change i≤m; omega)

/-- Every recorded quadratic one-gradient pair belongs to its actual chronological step/image transcript.
Use: the first-deletion retained window is computed from the real executed step sequence.
Article: main_krylov, apA:prop:short, retained steps s₁,…,s_m.
Proof: the actual new pair is the chosen step and its true quadratic image;
induction identifies the complete newest-first transcript. -/
theorem oneGradientRun_pairs_executed (method : OneGradientMethod E) (Q : E →L[ℝ] E) (g : E) (k : ℕ) :
    (oneGradientRun method (fun _ => Q) g k).pairs=
      executedPairs (fun j => method.step (oneGradientRun method (fun _ => Q) g j))
        (fun j => Q (method.step (oneGradientRun method (fun _ => Q) g j))) k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [oneGradientRun_pairs_succ,ih]; rfl

/-- Every actual noninitial full-memory XRFC step is the source's two-term bidiagonal reference-direction combination.
Use: the short-window obstruction uses actual recorded steps with their actual missed line components and trials.
Article: main_krylov, apA:prop:short, s_j=(α_(j−1)−τ_(j−1))d_(j−1)⁰+τ_jd_j⁰.
Proof: the proved actual output correction at the previous step supplies the
first component and the actual current virtual direction supplies the second. -/
theorem xrfc_full_step_succ (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hg : ∀ i<N, CG.gradient Q g i≠0)
    (ht : ∀ i<N, trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) g i)≠0)
    (j : ℕ) (hj : j+1<N) :
    let method := xrfcMethod fullMemory trial
    let H := fun i => oneGradientRun method (fun _ => Q) g i
    method.step (H (j+1))=(CG.length Q g j-trial (H j)) • CG.direction Q g j+
      trial (H (j+1)) • CG.direction Q g (j+1) := by
  have hc := xrfc_full_next_correction trial Q hQ hpos g N hg ht j (by omega)
  have hd := (xrfc_full_reference trial Q hQ hpos g N hg ht (j+1) (by omega)).2.2
  dsimp only at hc hd ⊢
  change virtualCorrection (selectedWindow fullMemory _) _+trial _ • windowDirection (selectedWindow fullMemory _) _=_
  rw [selectedWindow_full]
  change virtualCorrection (selectedWindow fullMemory _) _=_ at hc
  rw [selectedWindow_full] at hc
  rw [hc,hd]

end
end krylov.Methods
