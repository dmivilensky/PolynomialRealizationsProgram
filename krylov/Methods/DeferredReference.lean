import krylov.Methods.DeferredMethod

set_option autoImplicit false
/-!
Article: main_krylov, s3:def:DC and apB:lem:mu(d), actual global deferred quadratic consistency.
Use: derive the genuine full quadratic execution and CG consistency of
actual deferred cancellation, including real solved tails and all windows.
Source: true CG old-direction orthogonality, actual retained pair transcripts
and the genuine zero-residual deferred/untilted direction identity.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


/-- Every genuine reference recorded pair step is orthogonal to the true current quadratic CG gradient, including actual solved tails.
Use: Every genuine reference recorded pair step is orthogonal to the true current quadratic CG gradient, including actual solved tails.
Article: main_krylov, s3:def:DC and apB:lem:mu(d), actual global deferred quadratic consistency.
Proof: The real zero-gradient case is immediate; otherwise actual gradient persistence gives genuine prefix nonstagnation and true old-direction orthogonality. -/
theorem referencePairs_gradient_orthogonal (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ)
    (p : E × E) (hp : p∈referencePairs Q g k) : inner ℝ p.1 (CG.gradient Q g k)=0 := by
  -- Handle genuine solved tails before using real nonstagnating CG orthogonality.
  by_cases hz : CG.gradient Q g k=0
  · rw [hz,inner_zero_right]
  · have hpre (i : ℕ) (hi : i<k) : CG.gradient Q g i≠0 := by
      intro he
      exact hz (CG.gradient_eq_zero_of_le Q g he hi.le)
    obtain ⟨j,hj,rfl⟩ := referencePairs_mem Q g k p hp
    rw [referenceStep,real_inner_smul_left,(CG.invariant Q hQ hpos g k hpre).old_direction j hj,mul_zero]

/-- A genuine observed history with the actual CG gradient and true reference pair transcript has real zero retained-step residual coordinates for every memory.
Use: A genuine observed history with the actual CG gradient and true reference pair transcript has real zero retained-step residual coordinates for every memory.
Article: main_krylov, s3:def:DC and apB:lem:mu(d), actual global deferred quadratic consistency.
Proof: Every actual retained pair belongs to the genuine complete reference transcript and its true step is orthogonal to the real current gradient. -/
theorem history_reference_coordinates_zero (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ) (H : History E)
    (hpairs : H.pairs=referencePairs Q g k) (hgradient : H.gradient=CG.gradient Q g k) (memory : ℕ → ℕ) :
    coordinates (windowSteps (selectedWindow memory H)) H.gradient=0 := by
  apply window_coordinates_zero
  intro p hp
  have hm : p∈H.pairs := List.mem_of_mem_take hp
  rw [hpairs] at hm
  rw [hgradient]
  exact referencePairs_gradient_orthogonal Q hQ hpos g k p hm

/-- The genuine deferred-cancellation policy has exactly the real complete FC history on every positive quadratic, at every true iteration including solved tails.
Use: The genuine deferred-cancellation policy has exactly the real complete FC history on every positive quadratic, at every true iteration including solved tails.
Article: main_krylov, s3:def:DC and apB:lem:mu(d), actual global deferred quadratic consistency.
Proof: Induct over actual complete histories; the genuine old-step residual coordinates vanish, so the true deferred direction equals actual FC and both real correction phases are empty. -/
theorem deferredMethod_reference_run (memory : ℕ → ℕ) (hm : ∀ k, 0<k → 0<memory k)
    (N : ℕ) (a : ℝ) (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ) :
    methodRun (deferredMethod memory N a) (fun _ => Q) (fun _ => Q) g k=
      methodRun (fcMethod memory) (fun _ => Q) (fun _ => Q) g k := by
  -- Preserve the entire genuine observed history, using true zero old-step residuals at each real quadratic decision.
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [methodRun,methodRun,ih]
    let H := methodRun (fcMethod memory) (fun _ => Q) (fun _ => Q) g k
    have hs := fcMethod_static memory Q hQ hpos g (fun i _ => hm i) k
    have hz := history_reference_coordinates_zero Q hQ hpos g k H hs.2 hs.1 memory
    unfold methodAdvance
    rw [deferredMethod_direction_eq_FC memory N a H hz]
    rfl

/-- Actual deferred cancellation is globally genuinely CG-consistent on all positive quadratic data for every positive newest-pair memory rule.
Use: Actual deferred cancellation is globally genuinely CG-consistent on all positive quadratic data for every positive newest-pair memory rule.
Article: main_krylov, s3:def:DC and apB:lem:mu(d), actual global deferred quadratic consistency.
Proof: Its real complete quadratic history and true current direction equal actual FC; genuine quadratic consistency gives the actual positive CG direction scale and empty true correction tree. -/
theorem deferredMethod_consistent (memory : ℕ → ℕ) (hm : ∀ k, 0<k → 0<memory k) (N : ℕ) (a : ℝ) :
    CGConsistent (deferredMethod memory N a : ProbedMethod E) := by
  -- Obtain the actual positive current CG direction scale from genuine full-history FC consistency.
  intro Q hQ hpos g k
  have hs := fcMethod_static memory Q hQ hpos g (fun i _ => hm i) k
  have hz := history_reference_coordinates_zero Q hQ hpos g k _ hs.2 hs.1 memory
  obtain ⟨c,hc,hd,_⟩ := fcMethod_consistent memory hm Q hQ hpos g k
  refine ⟨c,hc,?_,by trivial⟩
  rw [deferredMethod_reference_run memory hm N a Q hQ hpos g k,deferredMethod_direction_eq_FC memory N a _ hz]
  exact hd
end
end krylov.Methods
