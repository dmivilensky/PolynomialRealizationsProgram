import krylov.LotkaVolterra.ExitInitial

/-!
Article: `main_krylov`, `apC:prop:LV`, finite exit for actual forward
trajectories outside the separating initial value. The theorem explicitly
records its interval of existence: an actual solution defined on the whole
forward half-line cannot remain in the lower wedge off the separator.
Construction of a stopped finite-time solution uses the separate local
existence/continuation interface.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set

theorem lower_finite_exit_of_global_solution {γ : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1)
    (G : SubcriticalGraph γ) {s U : ℝ → ℝ} (hU₀ : U 0 = 1)
    (hpos : ∀ t ≥ 0, 0 < s t ∧ 0 < U t)
    (hds : ∀ t ≥ 0, HasDerivAt s (2 * s t * (s t - 1 - γ * U t)) t)
    (hdU : ∀ t ≥ 0, HasDerivAt U (U t * (s t + 1 - U t)) t)
    (hne : s 0 ≠ G.σ 1) :
    ∃ t ≥ 0, saddleS γ ≤ s t ∨ s t + 1 ≤ U t := by
  by_contra! hno
  have hUm : MonotoneOn U (Ici 0) := by
    apply StrictMonoOn.monotoneOn
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
      (HasDerivAt.continuousOn fun t ht ↦ hdU t ht)
    intro t ht
    have ht₀ : 0 ≤ t := interior_subset ht
    rw [(hdU t ht₀).deriv]
    exact mul_pos (hpos t ht₀).2 (by linarith [(hno t ht₀).2])
  have hreg (t : ℝ) (ht : 0 ≤ t) :
      0 < s t ∧ s t < saddleS γ ∧ 1 ≤ U t ∧ U t < s t + 1 := by
    have hUge := hUm (a := (0 : ℝ)) (b := t) (mem_Ici.mpr le_rfl) ht ht
    rw [hU₀] at hUge
    exact ⟨(hpos t ht).1, (hno t ht).1, hUge, (hno t ht).2⟩
  exact hne (lower_nonexit_initial_on_graph hγ hγ₁ G hU₀ hreg hds hdU)

end
end krylov.LotkaVolterra
