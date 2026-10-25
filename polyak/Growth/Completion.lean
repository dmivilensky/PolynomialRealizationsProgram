import polyak.Growth.Envelope

/-!
Article: Appendix A, the original segment definition with data only at interior positions.
Use: endpoint completion changes neither positions nor Γ; it adds no regularity hypothesis.
Proof: arbitrary finite-table interpolation fills the two missing endpoint data.
-/

namespace polyak.Growth
noncomputable section
open Interpolation

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Article: original segment. Use: values and gradients are constrained only at interior positions. -/
structure RawSegment (A B β : ℝ) (n : ℕ) where
  /-- Article: positions e₀,…,eₙ₊₁. Use: the two endpoints need no supplied gradient. -/
  x : ℕ → E
  /-- Article: interior gradients. Use: data outside the interior are irrelevant. -/
  σ : ℕ → E
  /-- Article: interior values. Use: relative values with origin value zero. -/
  value : ℕ → ℝ
  /-- Article: all interior interpolation pairs. Use: no constraints on absent endpoint data. -/
  interpolation : ∀ i, 1 ≤ i → i ≤ n → ∀ j, 1 ≤ j → j ≤ n →
    |datumT x σ value i j| ≤ datumR x σ i j
  /-- Article: minimizer datum. Use: all supplied data include their pair with the origin. -/
  origin : ∀ i, 1 ≤ i → i ≤ n →
    |value i-(1/2 : ℝ)*inner ℝ (σ i) (x i)| ≤ (1/4 : ℝ)*(‖x i‖^2-‖σ i‖^2)
  /-- Article: normalized recurrence at the interior positions. -/
  recurrence : ∀ k, k < n → x (k+2)=A • x (k+1)+B • σ (k+1)-β • x k

variable {E}

/-- Article: forgetting endpoint data. Use: the completed model includes every original constraint. -/
def Segment.raw {A B β : ℝ} {n : ℕ} (s : Segment E A B β n) : RawSegment E A B β n where
  x := s.x
  σ := s.σ
  value := s.value
  interpolation i _ hi j _ hj := s.interpolation i (by omega) j (by omega)
  origin i _ hi := s.origin i (by omega)
  recurrence := s.recurrence

namespace RawSegment
variable [CompleteSpace E] {A B β : ℝ} {n : ℕ}

/-- Article: endpoint completion. Use: equivalence of the literal article model and complete tables. -/
theorem exists_completion (s : RawSegment E A B β n) :
    ∃ q : Segment E A B β n, q.x = s.x ∧
      ∀ i, 1 ≤ i → i ≤ n → q.σ i = s.σ i ∧ q.value i = s.value i := by
  let x : Option (Fin n) → E := fun i => i.elim 0 (fun j => s.x (j+1))
  let σ : Option (Fin n) → E := fun i => i.elim 0 (fun j => s.σ (j+1))
  let v : Option (Fin n) → ℝ := fun i => i.elim 0 (fun j => s.value (j+1))
  have htable : TableFeasible x σ v := by
    intro i j
    cases i with
    | none =>
      cases j with
      | none => simp [x, σ, v, datumT, datumR]
      | some j =>
        simpa only [x, σ, v, Option.elim, datumT, datumR, zero_add, sub_zero] using
          s.origin (j+1) (by omega) (by omega)
    | some i =>
      cases j with
      | none =>
        rw [datumT_antisymm x σ v none (some i), datumR_symm x σ (some i) none, abs_neg]
        simpa only [x, σ, v, Option.elim, datumT, datumR, zero_add, sub_zero] using
          s.origin (i+1) (by omega) (by omega)
      | some j => exact s.interpolation (i+1) (by omega) (by omega) (j+1) (by omega) (by omega)
  obtain ⟨ψ,hψ,hdata⟩ := (interpolation_iff (star := none) (x := x) (σ := σ) (values := v)
    rfl rfl rfl).mpr htable
  have hinterior (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
      ψ (s.x i)=s.value i ∧ gradient ψ (s.x i)=s.σ i := by
    simpa only [x, σ, v, Option.elim, Nat.sub_add_cancel hi] using
      hdata (some (⟨i-1, by omega⟩ : Fin n))
  let q := Segment.ofNormalized hψ s.x n (by
    intro k hk
    rw [(hinterior (k+1) (by omega) (by omega)).2]
    exact s.recurrence k hk)
  refine ⟨q,rfl,fun i hi hin => ?_⟩
  exact ⟨(hinterior i hi hin).2, (hinterior i hi hin).1⟩

end RawSegment

/-- Article: literal original Γ ratios. Use: no endpoint data are silently imposed. -/
def rawSegmentRatios (A B β : ℝ) (p : ℕ) : Set ℝ :=
  {r | ∃ d : ℕ, ∃ s : RawSegment (EuclideanSpace ℝ (Fin d)) A B β p,
    stateNorm s.x 0 ≠ 0 ∧ r=stateNorm s.x p/stateNorm s.x 0}

/-- Article: exact envelope definition. Use: completing endpoint data preserves the defining set of ratios. -/
theorem rawSegmentRatios_eq (A B β : ℝ) (p : ℕ) :
    rawSegmentRatios A B β p = segmentRatios A B β p := by
  ext r
  constructor
  · rintro ⟨d,s,hs,hr⟩
    obtain ⟨q,hq,_⟩ := s.exists_completion
    exact ⟨d,q,by simpa only [hq] using hs,by simpa only [hq] using hr⟩
  · rintro ⟨d,s,hs,hr⟩
    exact ⟨d,s.raw,hs,hr⟩

end
end polyak.Growth
