import krylov.Methods.TargetedFinalCorrection

set_option autoImplicit false
/-!
Article: main_krylov, apB:prop:consist, genuine fixed-reference CG execution.
Use: prove the actual target-relative one-correction method is exactly CG on its chosen true quadratic data, including solved tails.
Source: proved real retained-policy reference induction and the genuine zero inverse-model right-hand side at the designated target.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual targeted method has exactly the genuine CG gradients and recorded pairs on its chosen quadratic reference for every iteration.
Use: The actual targeted method has exactly the genuine CG gradients and recorded pairs on its chosen quadratic reference for every iteration.
Article: main_krylov, apB:prop:consist, genuine fixed-reference CG execution.
Proof: Use the actual retained-method reference invariant; at the real target iteration the incoming gradient equals the fixed target, so the genuine model query vanishes. -/
theorem targetedFinalMethod_static (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (N k : ℕ) :
    let H := methodRun (targetedFinalMethod N (CG.gradient Q g N)) (fun _ => Q) (fun _ => Q) g k
    H.gradient=CG.gradient Q g k ∧ H.pairs=referencePairs Q g k := by
  -- The real retained-method invariant proves the reference transcript before any target-model domain is used.
  apply retainedMethod_static fullMemory _ Q hQ hpos g (fun _ _ hk => hk)
  intro j H hg hp
  have hd : (fcMethod fullMemory).direction H=CG.direction Q g j :=
    retainedMethod_direction fullMemory _ Q hQ hpos g j H hg hp (fun _ hk => hk)
  have hgp : searchedGradient H.gradient ((fcMethod fullMemory).direction H)
      (Q ((fcMethod fullMemory).direction H))=CG.gradient Q g (j+1) := by rw [hg,hd];rfl
  -- At the designated true reference iteration the incoming post-search gradient equals the fixed target, so the actual query is zero.
  by_cases he : H.records.length+1=N
  · have hlen : H.records.length=j := by rw [← H.pairs_length,hp,referencePairs_length]
    have hj : j+1=N := by omega
    change ZeroCorrections (if H.records.length+1=N then _ else _) Q _
    rw [ite_eq_left he]
    change _=0 ∧ True
    refine ⟨?_,trivial⟩
    dsimp only [targetedCorrection,retainedMethod]
    dsimp only [fcMethod,retainedMethod] at hgp ⊢
    rw [hgp,hj,sub_self]
    have hz : coordinates (windowSteps (((fcMethod fullMemory).direction H,
        Q ((fcMethod fullMemory).direction H))::H.pairs)) (0 : E)=0 := by
      ext i
      exact inner_zero_right _
    dsimp only [fcMethod,retainedMethod] at hz
    rw [modelCoefficients_zero _ _ _ hz]
    simp only [combine,Pi.zero_apply,zero_smul,Finset.sum_const_zero]
  · change ZeroCorrections (if H.records.length+1=N then _ else _) Q _
    rw [ite_eq_right he]
    trivial

/-- Every actual chosen-reference direction of the genuine targeted method is exactly its true CG direction.
Use: Every actual chosen-reference direction of the genuine targeted method is exactly its true CG direction.
Article: main_krylov, apB:prop:consist, genuine fixed-reference CG execution.
Proof: The true reference gradients and recorded pairs identify the actual retained full-memory solve. -/
theorem targetedFinalMethod_reference_direction (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (N k : ℕ) :
    (targetedFinalMethod N (CG.gradient Q g N)).direction
      (methodRun (targetedFinalMethod N (CG.gradient Q g N)) (fun _ => Q) (fun _ => Q) g k)=
      CG.direction Q g k := by
  have h := targetedFinalMethod_static Q hQ hpos g N k
  exact retainedMethod_direction fullMemory _ Q hQ hpos g k _ h.1 h.2 (fun _ hk => hk)
end
end krylov.Methods
