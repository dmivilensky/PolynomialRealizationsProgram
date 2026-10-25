import polyak.Boundary.P5.DividedSlacks

/-!
Article: the critical three-cycle exception in the active-lag regime table.
Use: the four active constraints of the noncritical central branch are not
the complete raw zero set at t=0. The latter is the full residue-class set
CriticalPair, with arbitrarily large zero lags for either sign.
-/
noncomputable section
namespace polyak.Boundary.P5
open Spectral

theorem critical_raw_zero_iff {n : ℕ} (hn : 1≤n) {σ : ℝ}
    (hσ : σ= -1 ∨ σ=1) :
    actualRaw (1/2) 1 n σ (-1/2)=0 ↔ CriticalPair n σ := by
  have hT : chebT n (1 : ℝ)=1 := by simp [chebT]
  have hcases : n%3=0 ∨ n%3=1 ∨ n%3=2 := by omega
  unfold actualRaw g lagB
  rw [hT,chebT_cycle,chebU_lag_cycle n hn]
  rcases hσ with rfl | rfl <;>
    rcases hcases with hm | hm | hm <;> norm_num [CriticalPair,hm]

theorem critical_zero_lags_unbounded (N : ℕ) {σ : ℝ}
    (hσ : σ= -1 ∨ σ=1) :
    ∃ n : ℕ,N<n ∧ actualRaw (1/2) 1 n σ (-1/2)=0 := by
  refine ⟨3*(N+1),by omega,critical_actualRaw_zero (by omega) ?_⟩
  exact ⟨hσ,Or.inl (by omega)⟩

end polyak.Boundary.P5
