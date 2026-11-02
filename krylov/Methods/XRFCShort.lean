import krylov.Methods.XRFCShortPrefix

/-!
Article: main_krylov, apA:prop:short, actual arbitrary-length short-window counterexample.
Use: show that real sliding step-basis XRFC fails CG consistency at its first
deletion whenever the source's missed components and actual trials are nonzero.
Source: actual full-prefix comparison and the proved bidiagonal annihilator.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The first-deletion retained physical span contains only steps with chronological times 1 through m.
Use: apply the general bidiagonal obstruction to the actual newest-first short window.
Article: main_krylov, apA:prop:short, remaining window s₁,…,s_m.
Proof: every actual retained age is strictly below m and therefore refers to
chronological time m−age, which is one of the displayed noninitial steps. -/
theorem firstDeletionSpan_le (s y : ℕ → E) (m : ℕ) :
    pairSpan ((executedPairs s y (m+1)).take m)≤
      Submodule.span ℝ (Set.range (fun i : Fin m => s (i.val+1))) := by
  -- The indexing proof also covers the empty retained window.
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  have hi : i.val<m := by
    have h := i.isLt
    simp only [List.length_take,executedPairs_length] at h
    omega
  have hp : windowSteps ((executedPairs s y (m+1)).take m) i=s (m-i.val) := by
    change (((executedPairs s y (m+1)).take m)[i.val]).1=_
    rw [List.getElem_take,executedPairs_get s y (m+1) i.val (by omega)]
    simp only [Nat.add_sub_cancel]
  rw [hp]
  apply Submodule.subset_span
  exact ⟨⟨m-1-i.val,by omega⟩,congrArg s (by dsimp only; omega)⟩

/-- True nonstagnating chronological CG directions are independent through every finite prefix.
Use: the short-window counterexample uses genuine computed reference directions, not an assumed basis.
Article: main_krylov, apA:prop:short, independent m+1 CG directions.
Proof: positive self-curvature and actual pairwise conjugacy imply independence. -/
theorem cg_directionFamily_independent (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (N : ℕ)
    (hg : ∀ i<N, CG.gradient Q g i≠0) : LinearIndependent ℝ (fun i : Fin N => CG.direction Q g i.val) := by
  -- Both orientations of conjugacy follow from the same true symmetric positive operator.
  apply conjugate_independent Q hpos
  · intro i
    exact (CG.invariant_line_pos Q hpos g i.val
      (CG.invariant Q hQ hpos g i.val (fun j hj => hg j (hj.trans i.isLt))) (hg _ i.isLt)).1
  · intro i j hij
    have hk := CG.invariant Q hQ hpos g N hg
    rcases lt_or_gt_of_ne (Fin.val_injective.ne hij) with h | h
    · exact hk.conjugate _ _ h j.isLt.le
    · have he := hQ (CG.direction Q g i.val) (CG.direction Q g j.val)
      change inner ℝ (Q (CG.direction Q g i.val)) (CG.direction Q g j.val)=
        inner ℝ (CG.direction Q g i.val) (Q (CG.direction Q g j.val)) at he
      rw [← he,real_inner_comm]
      exact hk.conjugate _ _ h i.isLt.le

/-- Real sliding step-basis XRFC fails to produce the true CG virtual point at its first deletion for all nonzero missed components and trials.
Use: closes the general source counterexample for every window shorter than the active CG cycle, including zero memory.
Article: main_krylov, apA:prop:short, x̂_(m+1)≠x_(m+1)⁰.
Proof: before deletion the complete actual history equals full-memory XRFC;
its retained noninitial steps are the true bidiagonal combinations. Equality of the next virtual point would put the nonzero missed newest CG component in their span, contradicting the constructed annihilator. -/
theorem xrfc_short_not_consistent (m : ℕ) (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (hg : ∀ i<m+1, CG.gradient Q g i≠0)
    (ht : ∀ i<m+1, trial (oneGradientRun (xrfcMethod (slidingMemory m) trial) (fun _ => Q) g i)≠0)
    (he : ∀ i<m+1, CG.length Q g i-trial (oneGradientRun (xrfcMethod (slidingMemory m) trial) (fun _ => Q) g i)≠0) :
    (xrfcMethod (slidingMemory m) trial).outputDisplacement
      (oneGradientRun (xrfcMethod (slidingMemory m) trial) (fun _ => Q) g (m+1))≠CG.displacement Q g (m+1) := by
  -- Every algebraic obstruction is now instantiated with the real executed full-prefix step sequence.
  let method := xrfcMethod fullMemory trial
  let H := fun i => oneGradientRun method (fun _ => Q) g i
  let s := fun i => method.step (H i)
  let a := fun i => CG.length Q g i-trial (H i)
  let b := fun i => trial (H (i+1))
  let d := fun i : Fin (m+1) => CG.direction Q g i.val
  have hprefix := fun i hi => xrfc_sliding_prefix m trial (fun _ => Q) g i hi
  have htfull : ∀ i<m+1, trial (H i)≠0 := by
    intro i hi
    change trial (oneGradientRun method (fun _ => Q) g i)≠0
    rw [← hprefix i hi.le]
    exact ht i hi
  have ha : ∀ i<m+1, a i≠0 := by
    intro i hi
    change CG.length Q g i-trial (oneGradientRun method (fun _ => Q) g i)≠0
    rw [← hprefix i hi.le]
    exact he i hi
  have hsteps (i : Fin m) : s (i.val+1)=a i.val • d i.castSucc+b i.val • d i.succ :=
    xrfc_full_step_succ trial Q hQ hpos g (m+1) hg htfull i.val (by omega)
  have hspan : pairSpan ((executedPairs s (fun i => Q (s i)) (m+1)).take m)≤
      Submodule.span ℝ (Set.range (fun i : Fin m => a i.val • d i.castSucc+b i.val • d i.succ)) := by
    refine (firstDeletionSpan_le s (fun i => Q (s i)) m).trans ?_
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change s (i.val+1)∈_
    rw [hsteps]
    exact Submodule.subset_span ⟨i,rfl⟩
  have hno := bidiagonal_missed_not_mem m d (cg_directionFamily_independent Q hQ hpos g (m+1) hg)
    a b (fun i hi => ha i (by omega)) (fun i hi => htfull (i+1) (by omega)) (a m) (ha m (by omega))
  intro hout
  rw [hprefix (m+1) le_rfl] at hout
  have heval := xrfc_full_evaluated trial Q hQ hpos g (m+1) hg htfull m (by omega)
  change (H (m+1)).displacement = _ at heval
  have hmiss : (xrfcMethod (slidingMemory m) trial).output (H (m+1))=a m • d (Fin.last m) := by
    rw [OneGradientMethod.outputDisplacement,heval,CG.displacement_succ] at hout
    have hh := congrArg (fun v => v-(CG.displacement Q g m+trial (H m) • CG.direction Q g m)) hout
    rw [add_sub_cancel_left] at hh
    rw [hh]
    change _=(CG.length Q g m-trial (H m)) • CG.direction Q g m
    rw [sub_smul]
    abel
  apply hno
  apply hspan
  rw [← hmiss]
  have hw : selectedWindow (slidingMemory m) (H (m+1))=
      (executedPairs s (fun i => Q (s i)) (m+1)).take m := by
    change (H (m+1)).pairs.take m=_
    rw [oneGradientRun_pairs_executed]
  change virtualCorrection (selectedWindow (slidingMemory m) (H (m+1))) (H (m+1)).gradient∈_
  rw [← hw]
  exact combine_mem_span _ _

end
end krylov.Methods
