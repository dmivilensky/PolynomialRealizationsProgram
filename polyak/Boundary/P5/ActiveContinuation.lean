import polyak.Boundary.P5.StrictPrefix
import polyak.Boundary.P5.LocalFeasible

/-! Article: the exact four active signed constraints on the noncritical central branch. -/
noncomputable section
namespace polyak.Boundary.P5

/-- The finite strict checks and the uniform analytic tail cover every inactive signed lag. -/
theorem continuation_inactive_pos {h : ℝ} (hh : h∈Set.Ioc (0 : ℝ) (11791/500000))
    {n : ℕ} (hn : 1≤n) {σ : ℝ} (hσ : σ= -1 ∨ σ=1) (ha : ¬ActivePair n σ) :
    0<actualPrimal h (Selection.continuation h) n σ := by
  by_cases hN : n<24
  · exact continuation_inactive_prefix_pos hh hn hN hσ ha
  · have hb := (continuation_geometry hh).tail.toTailBounds
    simpa only [actualPrimal,branchU,branchX,mul_assoc] using
      normalized_twoAtom_pos hb n (by omega) σ hσ.symm

/-- Off h=0 the only zero slacks are L1,U2,U3,U5, exactly as in the classification table. -/
theorem continuation_active_iff {h : ℝ} (hh : h∈Set.Ioc (0 : ℝ) (11791/500000))
    {n : ℕ} (hn : 1≤n) {σ : ℝ} (hσ : σ= -1 ∨ σ=1) :
    actualPrimal h (Selection.continuation h) n σ=0 ↔ ActivePair n σ := by
  constructor
  · intro hz
    by_contra hnactive
    exact (continuation_inactive_pos hh hn hσ hnactive).ne' hz
  · intro ha
    obtain ⟨h1,h2,h3,h5⟩ := active_slacks_zero hh.1.le
      (Selection.continuation_source ⟨hh.1.le,hh.2⟩)
    rcases ha with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact h1
    · exact h2
    · exact h3
    · exact h5

end polyak.Boundary.P5
