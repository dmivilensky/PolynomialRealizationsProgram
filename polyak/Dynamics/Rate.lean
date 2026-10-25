import polyak.Dynamics.Instances
import Mathlib.Order.LiminfLimsup

/-!
Article: polyaksiopt, eq:WN.
Use: verify the dimension supremum and finiteness of the actual limsup rate.
-/

namespace polyak.Dynamics
noncomputable section
open Set Filter
open scoped Topology

/-- Article: eq:WN. Use: the unrestricted worst case equals the supremum over dimensions. -/
theorem worstAll_eq_dimension_sup {μ L α β : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (N : ℕ) :
    worstAll μ L α β N = sSup {r | ∃ d : ℕ, 0 < d ∧ r = worst μ L α β d N} := by
  let S : Set ℝ := {r | ∃ d : ℕ, 0 < d ∧ r = worst μ L α β d N}
  have hne : S.Nonempty := ⟨worst μ L α β 1 N, 1, by norm_num, rfl⟩
  have hb : BddAbove S := by
    refine ⟨(1+α*L+2*β)^N, ?_⟩
    rintro r ⟨d, _, rfl⟩
    exact worst_le hμ hL hα hβ d N
  have hn : 0 ≤ sSup S :=
    (worst_nonneg hμ hL hα hβ 1 N).trans (le_csSup hb ⟨1, by norm_num, rfl⟩)
  apply le_antisymm
  · apply csSup_le (insert_nonempty _ _)
    intro r hr
    rcases hr with rfl | ⟨d, hd, hr⟩
    · exact hn
    · exact (le_csSup (ratios_bddAbove hμ hL hα hβ d N) (mem_insert_of_mem _ hr)).trans
        (le_csSup hb ⟨d, hd, rfl⟩)
  · exact csSup_le hne (by
      rintro r ⟨d, hd, rfl⟩
      exact worst_le_worstAll hμ hL hα hβ hd N)

/-- Article: eq:WN. Use: all roots of the source finite-horizon bounds have a common majorant. -/
theorem worstAll_root_le {μ L α β : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (N : ℕ) :
    worstAll μ L α β N ^ ((N : ℝ)⁻¹) ≤ 1+α*L+2*β := by
  have hL0 := (hμ.trans hL).le
  have hK : 0 ≤ 1+α*L+2*β := by positivity
  by_cases hN : N=0
  · simp only [hN, Nat.cast_zero, inv_zero, Real.rpow_zero]
    nlinarith [mul_nonneg hα hL0]
  · calc
      _ ≤ ((1+α*L+2*β)^N) ^ ((N : ℝ)⁻¹) :=
        Real.rpow_le_rpow (worstAll_nonneg hμ hL hα hβ N)
          (worstAll_le hμ hL hα hβ N) (by positivity)
      _ = _ := Real.pow_rpow_inv_natCast hK hN

/-- Article: eq:WN. Use: the actual dimension-uniform limsup is a finite real bound. -/
theorem rate_le {μ L α β : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) : rate μ L α β ≤ 1+α*L+2*β := by
  apply limsup_le_of_le
    (isCoboundedUnder_le_of_le atTop (fun N =>
      Real.rpow_nonneg (worstAll_nonneg hμ hL hα hβ N) _))
  exact Eventually.of_forall (worstAll_root_le hμ hL hα hβ)

/-- Article: eq:WN. Use: the original limsup factor is nonnegative. -/
theorem rate_nonneg {μ L α β : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) : 0 ≤ rate μ L α β := by
  apply le_limsup_of_le (isBoundedUnder_of ⟨1+α*L+2*β,
    worstAll_root_le hμ hL hα hβ⟩)
  intro b hb
  obtain ⟨N, hN⟩ := hb.exists
  exact (Real.rpow_nonneg (worstAll_nonneg hμ hL hα hβ N) _).trans hN

end
end polyak.Dynamics
