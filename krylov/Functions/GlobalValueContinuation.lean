import krylov.Functions.ValueCentreMethod
import krylov.Methods.FinalizedReference

/-!
Article: main_krylov, def:classes(M^F) and thm:Fplanar, global continuation.
Use: compile any actual endpoint-value candidate into a genuine original
single final correction and continue by full-memory FC. Both the span
restriction and global quadratic CG consistency are derived for every
candidate reader, independently of the observed scalar values.
Source: the existing FinalizedReference continuation and true CG residual
orthogonality to the complete actual retained window.
-/
namespace krylov.Functions
noncomputable section
open krylov.Methods krylov.Reference krylov.Correction
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The current raw direction and all actual earlier retained steps.
The current probe is an actual observation, not an unknown matrix input.
Article: main_krylov, def:classes(M^F). -/
def valueCurrentWindow (m : ProbedMethod E) (H : History E) (z : E) : List (E × E) :=
  (m.direction H,z)::H.pairs

/-- Compile an endpoint-value candidate using only the actual window and
actual searched gradient. A zero projected residual forces zero motion;
the explicit membership guard enforces the retained-span rule for every
possible observed value-reader output. Article: def:classes(M^F). -/
def guardedValueCandidate (m : ProbedMethod E) (choose : History E → E → E)
    (H : History E) (z : E) : E := by
  classical
  let W := windowSteps (valueCurrentWindow m H z)
  let gp := searchedGradient H.gradient (m.direction H) z
  exact if coordinates W gp=0 then 0 else
    if choose H z∈Submodule.span ℝ (Set.range W) then choose H z else 0

/-- Exactly one evaluated correction point, followed by no further query.
The candidate reader may read the true retained endpoint scalar values;
it never receives an unknown operator. Article: thm:Fplanar. -/
def guardedValueAfter (m : ProbedMethod E) (choose : History E → E → E)
    (H : History E) (z : E) : CorrectionTree E :=
  .query (guardedValueCandidate m choose H z) (fun _=>.done)

/-- Every compiled candidate belongs to the actual retained step span,
for arbitrary value-reader decisions. Article: def:classes(M^F). -/
theorem guardedValueCandidate_mem (m : ProbedMethod E) (choose : History E → E → E)
    (H : History E) (z : E) :
    guardedValueCandidate m choose H z∈Submodule.span ℝ (Set.range (windowSteps (valueCurrentWindow m H z))) := by
  classical
  unfold guardedValueCandidate
  dsimp only
  split
  · exact Submodule.zero_mem _
  · split
    · assumption
    · exact Submodule.zero_mem _

/-- A genuine retained-span candidate that already vanishes on the observed
zero-residual branch is compiled exactly, without changing its selected
point or querying any additional data. Article: thm:Fplanar. -/
theorem guardedValueCandidate_eq (m : ProbedMethod E) (choose : History E → E → E)
    (H : History E) (z : E)
    (hspan : choose H z∈Submodule.span ℝ (Set.range (windowSteps (valueCurrentWindow m H z))))
    (hzero : coordinates (windowSteps (valueCurrentWindow m H z))
      (searchedGradient H.gradient (m.direction H) z)=0 → choose H z=0) :
    guardedValueCandidate m choose H z=choose H z := by
  classical
  unfold guardedValueCandidate
  dsimp only
  split
  · exact (hzero ‹_›).symm
  · rfl

/-- True positive-quadratic CG data make every compiled value correction
exactly zero, including actual solved tails and arbitrary direction scales.
Article: main_krylov, thm:Fplanar, global consistency. -/
theorem guardedValueAfter_reference_zero (m : ProbedMethod E) (choose : History E → E → E)
    (H : History E) (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ)
    (hg : H.gradient=CG.gradient Q g k) (hpairs : H.pairs=referencePairs Q g k)
    (c : ℝ) (hc : c≠0) (hd : m.direction H=c • CG.direction Q g k) :
    ZeroCorrections (guardedValueAfter m choose H (Q (m.direction H))) Q
      (searchedGradient H.gradient (m.direction H) (Q (m.direction H))) := by
  classical
  have hgp : searchedGradient H.gradient (m.direction H) (Q (m.direction H))=CG.gradient Q g (k+1) := by
    rw [hg,hd,map_smul,searchedGradient_smul _ _ _ hc]
    rfl
  have hcoord : coordinates (windowSteps (valueCurrentWindow m H (Q (m.direction H))))
      (searchedGradient H.gradient (m.direction H) (Q (m.direction H)))=0 := by
    rw [hgp]
    apply window_coordinates_zero
    intro p hp
    by_cases hz : CG.gradient Q g (k+1)=0
    · rw [hz,inner_zero_right]
    · have hpre i (hi : i<k+1) : CG.gradient Q g i≠0 := by
        intro hi0
        exact hz (CG.gradient_eq_zero_of_le Q g hi0 (by omega))
      have hk := CG.invariant Q hQ hpos g (k+1) hpre
      rcases List.mem_cons.mp hp with he | he
      · rw [he,hd,real_inner_smul_left,hk.old_direction k (by omega),mul_zero]
      · rw [hpairs] at he
        obtain ⟨j,hj,rfl⟩ := referencePairs_mem Q g k p he
        rw [referenceStep,real_inner_smul_left,hk.old_direction j (by omega),mul_zero]
  have hz : guardedValueCandidate m choose H (Q (m.direction H))=0 := by
    unfold guardedValueCandidate
    exact ite_eq_left hcoord
  simp only [guardedValueAfter,hz,ZeroCorrections]
  trivial

/-- The globally continued original method: unchanged gradient-only
prefix, one guarded endpoint-value final correction, then full-memory FC.
Article: main_krylov, def:classes(M^F) and thm:Fplanar. -/
def valueContinuedMethod (m : ProbedMethod E) (N : ℕ) (choose : History E → E → E) : ProbedMethod E where
  direction H := if H.records.length<N then m.direction H else (fcMethod fullMemory).direction H
  correction H z := if H.records.length+1=N then guardedValueAfter m choose H z
    else if H.records.length<N then m.correction H z else .done

/-- Every actual earlier operator history is preserved before the final
value correction, for every actual operator sequence. Article: thm:Fplanar. -/
theorem valueContinuedMethod_run_before (m : ProbedMethod E) (N : ℕ) (choose : History E → E → E)
    (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) (hk : k<N) :
    methodRun (valueContinuedMethod m N choose) A B g k=methodRun m A B g k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [methodRun,methodRun,ih (by omega)]
    unfold methodAdvance valueContinuedMethod
    dsimp only
    rw [methodRun_length,ite_eq_left (by omega),ite_eq_right (by omega),ite_eq_left (by omega)]

/-- The continued value method has the exact positive CG direction scale
and zero real correction tree at every true positive-quadratic iteration.
Article: main_krylov, thm:Fplanar, global class admission. -/
theorem valueContinuedMethod_reference_decision (m : ProbedMethod E) (hm : CGConsistent m)
    (N : ℕ) (choose : History E → E → E) (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ) (H : History E)
    (hg : H.gradient=CG.gradient Q g k) (hp : H.pairs=referencePairs Q g k)
    (hH : k<N → H=methodRun m (fun _=>Q) (fun _=>Q) g k) :
    ∃ c : ℝ, 0<c ∧ (valueContinuedMethod m N choose).direction H=c • CG.direction Q g k ∧
      ZeroCorrections ((valueContinuedMethod m N choose).correction H
        (Q ((valueContinuedMethod m N choose).direction H))) Q
        (searchedGradient H.gradient ((valueContinuedMethod m N choose).direction H)
          (Q ((valueContinuedMethod m N choose).direction H))) := by
  have hlen : H.records.length=k := by rw [←H.pairs_length,hp,referencePairs_length]
  by_cases hk : k<N
  · obtain ⟨c,hc,hd,hzero⟩ := hm Q hQ hpos g k
    have hh := hH hk
    subst H
    have hdir : (valueContinuedMethod m N choose).direction (methodRun m (fun _=>Q) (fun _=>Q) g k)=
        m.direction (methodRun m (fun _=>Q) (fun _=>Q) g k) := by
      exact ite_eq_left (by rw [methodRun_length]; exact hk)
    refine ⟨c,hc,hdir.trans hd,?_⟩
    rw [hdir]
    change ZeroCorrections (if _ then _ else if _ then _ else _) Q _
    rw [methodRun_length]
    by_cases he : k+1=N
    · rw [ite_eq_left he]
      exact guardedValueAfter_reference_zero m choose _ Q hQ hpos g k hg hp c hc.ne' hd
    · rw [ite_eq_right he,ite_eq_left hk]
      exact hzero
  · have hdir : (valueContinuedMethod m N choose).direction H=CG.direction Q g k := by
      change (if H.records.length<N then _ else _)=_
      rw [ite_eq_right (by omega)]
      exact retainedMethod_direction fullMemory (fun _ _=>.done) Q hQ hpos g k H hg hp (fun _ hj=>hj)
    refine ⟨1,zero_lt_one,by simpa only [one_smul] using hdir,?_⟩
    change ZeroCorrections (if H.records.length+1=N then _ else if H.records.length<N then _ else _) Q _
    rw [ite_eq_right (by omega),ite_eq_right (by omega)]
    trivial

/-- The actual globally continued histories have the genuine CG gradient
and complete real CG step/secant pairs, at every iteration and solved tail.
Article: main_krylov, thm:Fplanar. -/
theorem valueContinuedMethod_static (m : ProbedMethod E) (hm : CGConsistent m)
    (N : ℕ) (choose : History E → E → E) (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ) :
    let H := methodRun (valueContinuedMethod m N choose) (fun _=>Q) (fun _=>Q) g k
    H.gradient=CG.gradient Q g k ∧ H.pairs=referencePairs Q g k := by
  induction k with
  | zero => exact ⟨rfl,rfl⟩
  | succ k ih =>
    obtain ⟨c,hc,hd,hzero⟩ := valueContinuedMethod_reference_decision m hm N choose Q hQ hpos g k _ ih.1 ih.2
      (fun hk=>valueContinuedMethod_run_before m N choose _ _ g k hk)
    exact reference_advance_scaled _ Q g k _ ih.1 ih.2 hc.ne' hd hzero

/-- The actual full original value-aware method is globally CG-consistent,
including every iteration after its one final value correction.
There are no assumptions on the scalar reader's decisions.
Article: main_krylov, def:classes(M^F) and thm:Fplanar. -/
theorem valueContinuedMethod_consistent (m : ProbedMethod E) (hm : CGConsistent m)
    (N : ℕ) (choose : History E → E → E) : CGConsistent (valueContinuedMethod m N choose) := by
  intro Q hQ hpos g k
  have hs := valueContinuedMethod_static m hm N choose Q hQ hpos g k
  exact valueContinuedMethod_reference_decision m hm N choose Q hQ hpos g k _ hs.1 hs.2
    (fun hk=>valueContinuedMethod_run_before m N choose _ _ g k hk)

/-- At most one correction per iteration is preserved by the entire
global continuation, including the designated value step and all later FC
iterations. Article: main_krylov, definition of M^F. -/
theorem valueContinuedMethod_one (m : ProbedMethod E)
    (hm : ∀ H z,CorrectionTree.AtMostOne (m.correction H z)) (N : ℕ)
    (choose : History E → E → E) (H : History E) (z : E) :
    CorrectionTree.AtMostOne ((valueContinuedMethod m N choose).correction H z) := by
  classical
  change CorrectionTree.AtMostOne (if _ then _ else if _ then _ else _)
  split
  · exact fun _=>rfl
  · split
    · exact hm H z
    · trivial

/-- Compile a real retained-endpoint reader and its finite original value
rule into the full globally continued method. The reader is invoked only
in the designated final value-correction branch. Article: thm:Fplanar. -/
def continuedObservedValueMethod {N : ℕ} (m : ProbedMethod E) (hN : 0<N)
    (coeff : History E → FunctionSearchTranscript E N → Fin N → ℝ)
    (read : History E → E → FunctionSearchTranscript E N) : ProbedMethod E :=
  valueContinuedMethod m N (fun H z=>observedSpanFinalCorrection hN coeff H (read H z))

/-- Every actual endpoint-value reader and every retained coefficient rule
admit a genuine globally CG-consistent original method, at all iterations
after the final value correction as well. Article: thm:Fplanar. -/
theorem continuedObservedValueMethod_consistent {N : ℕ} (m : ProbedMethod E)
    (hm : CGConsistent m) (hN : 0<N)
    (coeff : History E → FunctionSearchTranscript E N → Fin N → ℝ)
    (read : History E → E → FunctionSearchTranscript E N) :
    CGConsistent (continuedObservedValueMethod m hN coeff read) :=
  valueContinuedMethod_consistent m hm N _

/-- The global compiler reproduces the finite actual retained-span rule
exactly whenever its reader reports the actual searched gradient and
actual retained steps. These are data dictionary conditions, not assumed
output or trajectory bounds. Article: thm:Fplanar, original class bridge. -/
theorem guardedValueCandidate_observed_rule {N : ℕ} (m : ProbedMethod E) (hN : 0<N)
    (coeff : History E → FunctionSearchTranscript E N → Fin N → ℝ)
    (read : History E → E → FunctionSearchTranscript E N) (H : History E) (z : E)
    (hg : observedFinalGradient (read H z)=searchedGradient H.gradient (m.direction H) z)
    (hs : ∀ i,(read H z).lineSteps i∈Submodule.span ℝ (Set.range (windowSteps (valueCurrentWindow m H z)))) :
    guardedValueCandidate m (fun H z=>observedSpanFinalCorrection hN coeff H (read H z)) H z=
      observedSpanFinalCorrection hN coeff H (read H z) := by
  classical
  let W := windowSteps (valueCurrentWindow m H z)
  let gp := searchedGradient H.gradient (m.direction H) z
  have hsub : Submodule.span ℝ (Set.range (read H z).lineSteps)≤Submodule.span ℝ (Set.range W) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact hs i
  apply guardedValueCandidate_eq
  · exact hsub (observedSpanFinalCorrection_mem hN coeff H (read H z))
  · intro hcoord
    have hker : Submodule.span ℝ (Set.range W)≤(innerSL ℝ gp).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      have hi := congrFun hcoord i
      change inner ℝ (W i) gp=0 at hi
      change inner ℝ gp (W i)=0
      rw [real_inner_comm]
      exact hi
    have hf := hker (hs ⟨0,hN⟩)
    change inner ℝ gp ((read H z).lineSteps ⟨0,hN⟩)=0 at hf
    unfold observedSpanFinalCorrection
    exact ite_eq_left (by rwa [hg])

/-- The entire globally continued method satisfies the original class's
direction and all-branch retained correction-span restrictions.
Article: main_krylov, def:classes(M^F). -/
theorem valueContinuedMethod_spanRestricted (m : ProbedMethod E)
    (hm : ProbedSpanRestricted fullMemory m) (N : ℕ) (choose : History E → E → E) :
    ProbedSpanRestricted fullMemory (valueContinuedMethod m N choose) := by
  intro H
  constructor
  · change (if H.records.length<N then _ else _)∈H.observedSpan
    split
    · exact (hm H).1
    · exact (fcMethod_spanRestricted fullMemory H).1
  · intro z
    change CorrectionTree.InSubspace
      (Submodule.span ℝ (Set.range (windowSteps
        (((if H.records.length<N then m.direction H else (fcMethod fullMemory).direction H),z)::selectedWindow fullMemory H))))
      (if H.records.length+1=N then guardedValueAfter m choose H z
        else if H.records.length<N then m.correction H z else .done)
    by_cases he : H.records.length+1=N
    · rw [ite_eq_left he,ite_eq_left (show H.records.length<N by omega),selectedWindow_full]
      exact ⟨guardedValueCandidate_mem m choose H z,fun _=>True.intro⟩
    · rw [ite_eq_right he]
      by_cases hk : H.records.length<N
      · rw [ite_eq_left hk,ite_eq_left hk]
        exact (hm H).2 z
      · simp only [ite_eq_right hk]
        trivial

/-- A literal globally continued original-class witness for the known-budget
endpoint-only centre. The value reader receives only the actual observed
history and current probe, and is used at the final correction only.
Article: main_krylov, thm:Fplanar, attained class upper. -/
def budgetedCentreGlobalMethod {N : ℕ} (S : E ≃L[ℝ] E) (B : ℝ) (hN : 0<N)
    (read : History E → E → FunctionSearchTranscript E N) : ProbedMethod E :=
  continuedObservedValueMethod (fcMethod fullMemory) hN
    (metricPlaneResponseCoefficients (budgetedPlaneCentreOutput B) S hN) read

/-- The actual centre's global continuation is CG-consistent on every
positive quadratic, through every later iteration and solved tail.
Article: main_krylov, thm:Fplanar. -/
theorem budgetedCentreGlobalMethod_consistent {N : ℕ} (S : E ≃L[ℝ] E) (B : ℝ) (hN : 0<N)
    (read : History E → E → FunctionSearchTranscript E N) :
    CGConsistent (budgetedCentreGlobalMethod S B hN read) :=
  continuedObservedValueMethod_consistent _ fullFC_consistent hN _ read

/-- The same actual centre method meets the original information-span
restrictions, independently of the observed endpoint values.
Article: main_krylov, def:classes(M^F) and thm:Fplanar. -/
theorem budgetedCentreGlobalMethod_admissible {N : ℕ} (S : E ≃L[ℝ] E) (B : ℝ) (hN : 0<N)
    (read : History E → E → FunctionSearchTranscript E N) :
    ProbedSpanRestricted fullMemory (budgetedCentreGlobalMethod S B hN read) :=
  valueContinuedMethod_spanRestricted _ (fcMethod_spanRestricted fullMemory) N _

/-- The complete continued centre executes at most one correction per
iteration, including its value-aware stage. Article: def:classes(M^F). -/
theorem budgetedCentreGlobalMethod_one {N : ℕ} (S : E ≃L[ℝ] E) (B : ℝ) (hN : 0<N)
    (read : History E → E → FunctionSearchTranscript E N) (H : History E) (z : E) :
    CorrectionTree.AtMostOne ((budgetedCentreGlobalMethod S B hN read).correction H z) :=
  valueContinuedMethod_one (fcMethod fullMemory) (fun _ _=>True.intro) N _ H z

/-- Every admitted finite-cycle value rule has a literal globally defined
original method with full-memory continuation. Article: thm:Fplanar. -/
def OneCorrectionValueMethod.globalMethod {N : ℕ} (M : OneCorrectionValueMethod E N)
    (hN : 0<N) (read : History E → E → FunctionSearchTranscript E N) : ProbedMethod E :=
  continuedObservedValueMethod M.gradientPolicy hN M.coefficients read

/-- The same original finite-cycle witness is CG-consistent at every
future iteration of its real continuation. Article: thm:Fplanar. -/
theorem OneCorrectionValueMethod.globalMethod_consistent {N : ℕ} (M : OneCorrectionValueMethod E N)
    (hN : 0<N) (read : History E → E → FunctionSearchTranscript E N) :
    CGConsistent (M.globalMethod hN read) :=
  continuedObservedValueMethod_consistent M.gradientPolicy M.consistent hN M.coefficients read

/-- All original observed-span restrictions hold for the actual continued
witness at every iteration, not merely on quadratics. Article: thm:Fplanar. -/
theorem OneCorrectionValueMethod.globalMethod_admissible {N : ℕ} (M : OneCorrectionValueMethod E N)
    (hN : 0<N) (read : History E → E → FunctionSearchTranscript E N) :
    ProbedSpanRestricted fullMemory (M.globalMethod hN read) :=
  valueContinuedMethod_spanRestricted M.gradientPolicy M.admissible N _

/-- The real global witness keeps the source's one-correction limit
through its final value stage and all later iterations. Article: thm:Fplanar. -/
theorem OneCorrectionValueMethod.globalMethod_one {N : ℕ} (M : OneCorrectionValueMethod E N)
    (hN : 0<N) (read : History E → E → FunctionSearchTranscript E N) (H : History E) (z : E) :
    CorrectionTree.AtMostOne ((M.globalMethod hN read).correction H z) :=
  valueContinuedMethod_one M.gradientPolicy M.prefix_one N _ H z

/-- On genuine retained endpoint data the global compiler executes exactly
the finite rule's selected one-query correction, including its zero branch.
Thus the finite attained centre and the full original-class witness have
the very same physical final output. Article: thm:Fplanar. -/
theorem OneCorrectionValueMethod.globalMethod_final_exact {N : ℕ} (M : OneCorrectionValueMethod E N)
    (hN : 0<N) (read : History E → E → FunctionSearchTranscript E N) (H : History E) (z : E)
    (hfinal : H.records.length+1=N)
    (hg : observedFinalGradient (read H z)=searchedGradient H.gradient (M.gradientPolicy.direction H) z)
    (hs : ∀ i,(read H z).lineSteps i∈Submodule.span ℝ
      (Set.range (windowSteps (valueCurrentWindow M.gradientPolicy H z)))) :
    (M.globalMethod hN read).correction H z=
      observedSpanFinalTree hN M.coefficients H (read H z) := by
  change (if H.records.length+1=N then _ else if _ then _ else _)=_
  rw [ite_eq_left hfinal]
  unfold guardedValueAfter observedSpanFinalTree
  rw [guardedValueCandidate_observed_rule M.gradientPolicy hN M.coefficients read H z hg hs]

end
end krylov.Functions
