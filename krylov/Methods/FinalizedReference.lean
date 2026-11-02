import krylov.Methods.LatestAfterReference

set_option autoImplicit false
/-!
Article: main_krylov, thm:select and apB:lem:mu(a), genuine global CG consistency after final correction.
Use: prove the actual arbitrary-method final latest-information wrapper
is globally CG-consistent on every true positive quadratic, including
all later iterations and genuine solved tails.
Source: actual preserved earlier histories, real zero final model queries,
true complete CG pair transcripts and genuine full-memory FC continuation.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual final-correction wrapper chooses a genuine positive CG direction multiple and has real zero corrections on every true quadratic history with the actual CG gradient and pair transcript.
Use: The actual final-correction wrapper chooses a genuine positive CG direction multiple and has real zero corrections on every true quadratic history with the actual CG gradient and pair transcript.
Article: main_krylov, thm:select and apB:lem:mu(a), genuine global CG consistency after final correction.
Proof: Before the true horizon, exact real prefix identity transfers original global consistency and genuine quadratic orthogonality makes the actual appended model query zero. After the real horizon, the actual full pair transcript gives the genuine FC direction and empty corrections. -/
theorem finalizedMethod_reference_decision (m : ProbedMethod E) (hm : CGConsistent m) (N : ℕ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ) (H : History E)
    (hg : H.gradient=CG.gradient Q g k) (hp : H.pairs=referencePairs Q g k)
    (hH : k<N → H=methodRun m (fun _ => Q) (fun _ => Q) g k) :
    ∃ c : ℝ, 0<c ∧ (finalizedMethod m N).direction H=c • CG.direction Q g k ∧
      ZeroCorrections ((finalizedMethod m N).correction H (Q ((finalizedMethod m N).direction H))) Q
        (searchedGradient H.gradient ((finalizedMethod m N).direction H) (Q ((finalizedMethod m N).direction H))) := by
  -- Derive the genuine iteration count from the actual pair transcript before comparing the true original and later FC branches.
  have hlen : H.records.length=k := by rw [← H.pairs_length,hp,referencePairs_length]
  by_cases hk : k<N
  · obtain ⟨c,hc,hd,hzero⟩ := hm Q hQ hpos g k
    have hh := hH hk
    subst H
    have hn : (methodRun m (fun _ => Q) (fun _ => Q) g k).records.length<N := by rw [methodRun_length];exact hk
    have hdir := finalizedMethod_direction_before m N _ hn
    refine ⟨c,hc,hdir.trans hd,?_⟩
    rw [hdir]
    dsimp only [finalizedMethod]
    rw [methodRun_length]
    by_cases he : k+1=N
    · rw [ite_eq_left he]
      apply CorrectionTree.zeroCorrections_follow _ _ Q _ hzero
      have hs : searchedGradient (methodRun m (fun _ => Q) (fun _ => Q) g k).gradient
          (m.direction (methodRun m (fun _ => Q) (fun _ => Q) g k))
          (Q (m.direction (methodRun m (fun _ => Q) (fun _ => Q) g k)))=CG.gradient Q g (k+1) := by
        rw [hg,hd,map_smul,searchedGradient_smul _ _ _ hc.ne']
        rfl
      rw [hs]
      exact latestAfter_reference_zero m _ Q hQ hpos g k hp c hd
    · rw [ite_eq_right he,ite_eq_left hk]
      exact hzero
  · have hdir : (finalizedMethod m N).direction H=CG.direction Q g k := by
      rw [finalizedMethod_direction_after m N H (by omega)]
      exact retainedMethod_direction fullMemory (fun _ _ => .done) Q hQ hpos g k H hg hp (fun _ hj => hj)
    refine ⟨1,zero_lt_one,by simpa only [one_smul] using hdir,?_⟩
    change ZeroCorrections (if H.records.length+1=N then _ else if H.records.length<N then _ else _) Q _
    rw [ite_eq_right (by omega),ite_eq_right (by omega)]
    trivial

/-- The actual final latest-information wrapper has precisely the true CG gradient and complete stored step/secant pair transcript on every genuine quadratic iteration, including all real later and solved-tail indices.
Use: The actual final latest-information wrapper has precisely the true CG gradient and complete stored step/secant pair transcript on every genuine quadratic iteration, including all real later and solved-tail indices.
Article: main_krylov, thm:select and apB:lem:mu(a), genuine global CG consistency after final correction.
Proof: Induct through genuine actual histories using the real positive direction scale and true zero-correction decision, then apply the proved actual scaled quadratic reference advance. -/
theorem finalizedMethod_static (m : ProbedMethod E) (hm : CGConsistent m) (N : ℕ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ) :
    let H := methodRun (finalizedMethod m N) (fun _ => Q) (fun _ => Q) g k
    H.gradient=CG.gradient Q g k ∧ H.pairs=referencePairs Q g k := by
  -- Preserve the genuine actual gradient and complete stored CG pair transcript through every real wrapped iteration.
  induction k with
  | zero => exact ⟨rfl,rfl⟩
  | succ k ih =>
    obtain ⟨c,hc,hd,hzero⟩ := finalizedMethod_reference_decision m hm N Q hQ hpos g k _ ih.1 ih.2
      (fun hk => finalizedMethod_run_before m N _ _ g k hk)
    exact reference_advance_scaled _ Q g k _ ih.1 ih.2 hc.ne' hd hzero

/-- Appending the actual designated final latest-information correction and continuing by genuine full-memory FC preserves global CG consistency of every real original globally CG-consistent method.
Use: Appending the actual designated final latest-information correction and continuing by genuine full-memory FC preserves global CG consistency of every real original globally CG-consistent method.
Article: main_krylov, thm:select and apB:lem:mu(a), genuine global CG consistency after final correction.
Proof: Use the genuine complete quadratic transcript and its actual positive direction and zero-correction decision at every real iteration. -/
theorem finalizedMethod_consistent (m : ProbedMethod E) (hm : CGConsistent m) (N : ℕ) :
    CGConsistent (finalizedMethod m N) := by
  intro Q hQ hpos g k
  have hs := finalizedMethod_static m hm N Q hQ hpos g k
  exact finalizedMethod_reference_decision m hm N Q hQ hpos g k _ hs.1 hs.2
    (fun hk => finalizedMethod_run_before m N _ _ g k hk)
end
end krylov.Methods
