import polyak.Boundary.P5.DividedSlacks
import polyak.Boundary.P5.LocalImplicit
import polyak.Boundary.P5.Active

/-!
Article: Theorem p5local, simultaneous feasibility of the finite lag prefix.
Use: exact active equations and genuine divided-slack limits give one common
neighborhood for every lag below the analytically controlled uniform tail.
-/
noncomputable section
namespace polyak.Boundary.P5
open Spectral Filter
open scoped Topology

/-- Article: every fixed signed lag is feasible along the actual local branch. -/
theorem eventually_branch_primal_nonneg (n : ℕ) (hn : 1≤n) (σ : ℝ) (hs : σ= -1 ∨ σ=1) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), 0≤actualPrimal h (localBranch h) n σ := by
  by_cases ha : ActivePair n σ
  · filter_upwards [localBranch_equations.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with h hz hh
    obtain ⟨h1,h2,h3,h5⟩ := active_slacks_zero hh.le hz
    rcases ha with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact h1.ge
    · exact h2.ge
    · exact h3.ge
    · exact h5.ge
  · by_cases hc : CriticalPair n σ
    · exact (eventually_actualPrimal_pos_critical localBranch_analyticAt.continuousAt
        localBranch_zero hn hc ha).mono fun _ h => h.le
    · exact ((eventually_actualPrimal_pos_noncritical localBranch_analyticAt.continuousAt
        localBranch_zero hn hs hc).filter_mono nhdsWithin_le_nhds).mono fun _ h => h.le

/-- Article: all 46 signed constraints below lag 24 hold on one common right neighborhood. -/
theorem eventually_branch_primal_prefix :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ n : ℕ, 1≤n → n<24 →
      ∀ σ : ℝ, (σ= -1 ∨ σ=1) → 0≤actualPrimal h (localBranch h) n σ := by
  have hf (n : Fin 24) (s : Bool) :
      ∀ᶠ h in 𝓝[>] (0 : ℝ), 1≤(n : ℕ) →
        0≤actualPrimal h (localBranch h) n (if s then 1 else -1) := by
    by_cases hn : 1≤(n : ℕ)
    · have hs : ((if s then 1 else -1) : ℝ)= -1 ∨ ((if s then 1 else -1) : ℝ)=1 := by
        cases s <;> simp
      exact (eventually_branch_primal_nonneg n hn _ hs).mono fun _ h _ => h
    · exact Eventually.of_forall fun _ h => (hn h).elim
  have hall : ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ n : Fin 24, ∀ s : Bool,
      1≤(n : ℕ) → 0≤actualPrimal h (localBranch h) n (if s then 1 else -1) := by
    exact eventually_all.mpr fun n => eventually_all.mpr (hf n)
  filter_upwards [hall] with h hh n hn hn24 σ hs
  rcases hs with rfl | rfl
  · simpa only [Bool.false_eq_true,ite_false] using hh ⟨n,hn24⟩ false hn
  · simpa only [ite_true] using hh ⟨n,hn24⟩ true hn

end polyak.Boundary.P5
