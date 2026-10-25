import polyak.Growth.Envelope

/-!
Article: Appendix A, admissible segments and growth envelope.
Use: extend any finite admissible segment to one genuine infinite trajectory.
Proof: interpolate its finite table including the minimizer, then run the free recurrence.
-/

namespace polyak.Growth
noncomputable section
open polyak.Interpolation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Article: free two-position initialization. Use: no initial zero-impulse restriction. -/
def freePair (σ : E → E) (A B β : ℝ) (a b : E) : ℕ → E × E
  | 0 => (a,b)
  | k+1 => let p := freePair σ A B β a b k
    (p.2, A • p.2+B • σ p.2-β • p.1)

/-- Article: free trajectory positions. Use: the first component of consecutive pairs. -/
def freePosition (σ : E → E) (A B β : ℝ) (a b : E) (k : ℕ) : E :=
  (freePair σ A B β a b k).1

omit [CompleteSpace E] in
/-- Article: free dynamics. Use: exact second-order normalized recurrence. -/
theorem freePosition_recurrence (σ : E → E) (A B β : ℝ) (a b : E) (k : ℕ) :
    freePosition σ A B β a b (k+2) =
      A • freePosition σ A B β a b (k+1) +
      B • σ (freePosition σ A B β a b (k+1))-β • freePosition σ A B β a b k := rfl

/-- Article: genuine infinite normalized trajectory. Use: every finite prefix is admissible. -/
structure Run (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A B β : ℝ) where
  /-- Article: potential. Use: retain one actual function for the entire trajectory. -/
  ψ : E → ℝ
  /-- Article: normalized function class. Use: exact differentiability and gradient bound. -/
  normalized : NormalizedSmooth ψ
  /-- Article: positions. Use: arbitrary free initialization. -/
  x : ℕ → E
  /-- Article: dynamics. Use: the recurrence holds at every index. -/
  recurrence : ∀ k, x (k+2) = A • x (k+1)+B • gradient ψ (x (k+1))-β • x k

/-- Article: admissible infinite prefixes. Use: apply finite-segment results at any horizon. -/
def Run.segment {A B β : ℝ} (r : Run E A B β) (n : ℕ) : Segment E A B β n :=
  Segment.ofNormalized r.normalized r.x n (fun k _ => r.recurrence k)

/-- Article: interpolation of finite segments. Use: the endpoint gradients and values
are interpolated together with all interior data and the minimizer. -/
theorem Segment.exists_potential {A B β : ℝ} {n : ℕ} (s : Segment E A B β n) :
    ∃ ψ : E → ℝ, NormalizedSmooth ψ ∧
      ∀ k, k ≤ n+1 → ψ (s.x k) = s.value k ∧ gradient ψ (s.x k) = s.σ k := by
  let x : Option (Fin (n+2)) → E := fun j => j.elim 0 (fun i => s.x i)
  let σ : Option (Fin (n+2)) → E := fun j => j.elim 0 (fun i => s.σ i)
  let v : Option (Fin (n+2)) → ℝ := fun j => j.elim 0 (fun i => s.value i)
  have hn (j : Fin (n+2)) : |datumT x σ v none (some j)| ≤ datumR x σ none (some j) := by
    simpa only [datumT, datumR, x, σ, v, Option.elim_none, Option.elim_some,
      zero_add, sub_zero] using s.origin j (by omega)
  have htable : TableFeasible x σ v := by
    intro i j
    cases i with
    | none =>
      cases j with
      | none => simp [datumT, datumR, x, σ, v]
      | some j => exact hn j
    | some i =>
      cases j with
      | none =>
        rw [datumT_antisymm, abs_neg, datumR_symm]
        exact hn i
      | some j => exact s.interpolation i (by omega) j (by omega)
  obtain ⟨ψ,hψ,hdata⟩ := exists_normalized_interpolant htable none rfl rfl rfl
  refine ⟨ψ,hψ, fun k hk => ?_⟩
  exact hdata (some ⟨k,by omega⟩)

/-- Article: extension of finite admissible segments. Use: infinite energy arguments
apply to every segment in Γ, with both initial positions and the whole prefix preserved. -/
theorem Segment.exists_run {A B β : ℝ} {n : ℕ} (s : Segment E A B β n) :
    ∃ r : Run E A B β, ∀ k, k ≤ n+1 → r.x k = s.x k := by
  obtain ⟨ψ,hψ,hdata⟩ := s.exists_potential
  let r : Run E A B β :=
    ⟨ψ,hψ,freePosition (gradient ψ) A B β (s.x 0) (s.x 1),
      freePosition_recurrence (gradient ψ) A B β (s.x 0) (s.x 1)⟩
  have hp (k : ℕ) (hk : k ≤ n) :
      freePair (gradient ψ) A B β (s.x 0) (s.x 1) k = (s.x k,s.x (k+1)) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [freePair, ih (by omega)]
      dsimp
      rw [(hdata (k+1) (by omega)).2, ← s.recurrence k (by omega)]
  refine ⟨r,fun k hk => ?_⟩
  cases k with
  | zero => rfl
  | succ k =>
    change (freePair (gradient ψ) A B β (s.x 0) (s.x 1) (k+1)).1 = _
    rw [freePair, hp k (by omega)]

end
end polyak.Growth
