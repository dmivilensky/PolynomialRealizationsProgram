import krylov.Functions.RFCReferenceChange
import Mathlib.Topology.MetricSpace.Thickening

/-!
Article: main_krylov, s7:N and thm:Htransfer, deriving the frozen reference set.
Use: remove any additional minimizer-Hessian nondegeneracy assumption from
actual own-first-secant compact hypotheses. Source: genuine joint CG prefix
analyticity and a compact closed metric tube; no perturbed flag is supplied.
-/
namespace krylov.Functions
noncomputable section
open Set Metric Filter krylov.Methods krylov.Reference krylov.Stability
open scoped InnerProductSpace Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

set_option maxHeartbeats 800000 in
omit [CompleteSpace E] in
/-- Every genuine compact positive nonstagnating observed-reference family
has one derived compact full frozen-gradient set which contains all nearby
minimizer-Hessian references. The latter is a conclusion, not an independent
nondegeneracy hypothesis. Article: main_krylov, s7:N and thm:Htransfer. -/
theorem compact_own_reference_frozen_tube (Q : E →L[ℝ] E) (N : ℕ)
    (K : Set ((E →L[ℝ] E) × E)) (hK : IsCompact K)
    (hquad : ∀ z∈K, z.1.toLinearMap.IsSymmetric ∧
      (∀ v, v≠0 → 0 < inner ℝ v (z.1 v)) ∧ ∀ i<N, CG.gradient z.1 z.2 i≠0) :
    ∃ δ : ℝ, 0<δ ∧ ∃ G : Set E, IsCompact G ∧
      (∀ g∈G, ∀ i<N, CG.gradient Q g i≠0) ∧
      ∀ A : E →L[ℝ] E, ∀ g g₀ : E, (A,g)∈K → ‖(A-Q,g-g₀)‖≤δ → g₀∈G := by
  let S := {z : (E →L[ℝ] E) × E | ∀ i<N, CG.gradient z.1 z.2 i≠0}
  have hsub : K⊆interior S := by
    intro z hz
    apply mem_interior_iff_mem_nhds.mpr
    have hi (i : Fin N) : ∀ᶠ p : (E →L[ℝ] E) × E in 𝓝 z, CG.gradient p.1 p.2 i.val≠0 := by
      have ha := (cg_prefix_analytic
        (fun p : (E →L[ℝ] E) × E=>p.1) (fun p=>p.2) z
        analyticAt_fst analyticAt_snd (hquad z hz).1 (hquad z hz).2.1 i.val
        (fun j hj=>(hquad z hz).2.2 j (hj.trans i.isLt))).1
      exact ha.continuousAt.eventually_ne ((hquad z hz).2.2 i.val i.isLt)
    have hh := Filter.eventually_all.mpr hi
    exact hh.mono (fun p hp i hi=>hp (⟨i,hi⟩ : Fin N))
  obtain ⟨δ₁,hδ₁,htube⟩ := hK.exists_cthickening_subset_open isOpen_interior hsub
  obtain ⟨δ₂,hδ₂,hcompact⟩ := hK.exists_isCompact_cthickening
  let δ := min δ₁ δ₂
  have hδ : 0<δ := lt_min hδ₁ hδ₂
  have hcompact' : IsCompact (cthickening δ K) := hcompact.of_isClosed_subset isClosed_cthickening
    (cthickening_mono (min_le_right _ _) K)
  let C := cthickening δ K ∩ {z : (E →L[ℝ] E) × E | z.1=Q}
  have hC : IsCompact C := hcompact'.inter_right (isClosed_eq continuous_fst continuous_const)
  let G := Prod.snd '' C
  refine ⟨δ,hδ,G,hC.image continuous_snd,?_,?_⟩
  · intro g hg i hi
    obtain ⟨z,hz,rfl⟩ := hg
    have hh := interior_subset (htube (cthickening_mono (min_le_left _ _) K hz.1)) i hi
    rw [hz.2] at hh
    exact hh
  · intro A g g₀ hown hnear
    have hdist : dist (Q,g₀) (A,g)≤δ := by
      rw [dist_eq_norm]
      have he : (Q,g₀)-(A,g)= -(A-Q,g-g₀) := by ext <;> simp
      rw [he,norm_neg]
      exact hnear
    exact ⟨(Q,g₀),⟨mem_cthickening_of_dist_le _ _ δ K hown hdist,rfl⟩,rfl⟩

end
end krylov.Functions
