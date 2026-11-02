import krylov.Methods.FinalizedMethod

set_option autoImplicit false
/-!
Article: main_krylov, thm:select and apB:lem:mu(a), actual final model correction quadratic consistency.
Use: prove the genuine final full-model query is exactly zero on every
actual quadratic CG transcript, including all true solved-tail cases
and every real reference direction normalization.
Source: actual CG residual orthogonality, genuine stored-pair transcripts
and real zero-right-hand-side model corrections without an inverse-domain assumption.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual final latest-information correction query vanishes on every genuine quadratic CG transcript, including stopped tails and arbitrary true scalar direction normalization.
Use: The actual final latest-information correction query vanishes on every genuine quadratic CG transcript, including stopped tails and arbitrary true scalar direction normalization.
Article: main_krylov, thm:select and apB:lem:mu(a), actual final model correction quadratic consistency.
Proof: A zero true next gradient gives an actual zero projected right-hand side. Otherwise real nonstagnation yields genuine CG orthogonality to the current direction and every actual stored earlier step, so the real model correction is exactly zero. -/
theorem latestAfter_reference_zero (m : ProbedMethod E) (H : History E)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ)
    (hpairs : H.pairs=referencePairs Q g k) (c : ℝ) (hd : m.direction H=c • CG.direction Q g k) :
    ZeroCorrections (latestAfter m H (Q (m.direction H)) (CG.gradient Q g (k+1))) Q (CG.gradient Q g (k+1)) := by
  -- Actual CG orthogonality annihilates the true model right-hand side; genuine solved tails need no artificial nonsingular model domain.
  apply repeatedModelTree_zero
  by_cases hz : CG.gradient Q g (k+1)=0
  · rw [hz]
    ext i
    exact inner_zero_right _
  · have hpre (i : ℕ) (hi : i<k+1) : CG.gradient Q g i≠0 := by
      intro he
      exact hz (CG.gradient_eq_zero_of_le Q g he (by omega))
    have hk := CG.invariant Q hQ hpos g (k+1) hpre
    apply window_coordinates_zero
    intro p hp
    rcases List.mem_cons.mp hp with he | he
    · rw [he,hd,real_inner_smul_left,hk.old_direction k (by omega),mul_zero]
    · rw [hpairs] at he
      obtain ⟨j,hj,rfl⟩ := referencePairs_mem Q g k p he
      rw [referenceStep,real_inner_smul_left,hk.old_direction j (by omega),mul_zero]
end
end krylov.Methods
