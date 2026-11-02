import krylov.Stability.CompactFirstOrder

/-!
Article: main_krylov, thm:RFCS, uniform genuine compact domain tubes.
Use: Upgrade true pointwise neighborhood properties around every compact
reference to one common full reference/source tube.
Source: metric closed thickening of a compact subset of an open set,
IsCompact.exists_cthickening_subset_open in mathlib.
-/

namespace krylov.Stability
noncomputable section
open Set Filter Topology Metric
variable {R P : Type*} [NormedAddCommGroup R]
    [NormedAddCommGroup P]

/-- Every genuine neighborhood property at all points of a compact reference family holds throughout one common full reference/source tube.
Use: Derive actual uniform search, inverse and observed-gate domains from their true reference neighborhoods.
Article: main_krylov, thm:RFCS, compact genuine domain localization.
Proof: The genuine reference product lies in the interior of the property set; its compactness gives one closed thickening inside that interior.
-/
theorem compact_reference_eventual_tube (p : R × P → Prop) (K : Set R) (hK : IsCompact K)
    (hp : ∀ x∈K, ∀ᶠ z in 𝓝 (x,(0 : P)), p z) :
    ∃ δ : ℝ, 0<δ ∧ ∀ x∈K, ∀ v : R, ∀ θ : P, ‖(v,θ)‖≤δ → p (x+v,θ) := by
  let K₀ : Set (R × P) := K×ˢ{(0 : P)}
  have hK₀ : IsCompact K₀ := hK.prod isCompact_singleton
  have hsub : K₀⊆interior {z | p z} := by
    rintro ⟨x,θ⟩ ⟨hx,hθ⟩
    rw [Set.mem_singleton_iff] at hθ
    change θ=(0 : P) at hθ
    subst θ
    exact mem_interior_iff_mem_nhds.mpr (hp x hx)
  obtain ⟨δ,hδ,hbound⟩ := hK₀.exists_cthickening_subset_open isOpen_interior hsub
  refine ⟨δ,hδ,?_⟩
  intro x hx v θ hθ
  apply interior_subset (hbound _)
  apply mem_cthickening_of_dist_le (x+v,θ) (x,0) δ K₀ ⟨hx,rfl⟩
  simpa only [dist_eq_norm,Prod.mk_sub_mk,add_sub_cancel_left,sub_zero] using hθ

end
end krylov.Stability
