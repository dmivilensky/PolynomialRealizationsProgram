import krylov.AnalyticTools.RescaledFlow
import Mathlib.Analysis.ODE.ExistUnique

/-!
Article: main_krylov, thm:value, the initial analytic right germ.
Use: extend an actual one-sided ODE solution analytically through its initial
point. Compact-range local Lipschitz estimates identify a genuine two-sided
Picard solution with the original right-hand trajectory.
Source: mathlib Picard--Lindelöf and the proved analytic path-field construction.
-/

namespace krylov.AnalyticTools
noncomputable section
open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A genuine right-hand integral curve has a two-sided analytic extension
when its actual field has the stated analytic lift. No analytic-flow axiom
or analyticity hypothesis on the original curve is used. -/
theorem exists_analytic_right_extension {F : E → E}
    (hF : ∀ z, ContDiffAt ℝ 1 F z)
    (P : C(PathDomain, E) → C(PathDomain, E))
    (hP : ∀ f u, P f u = F (f u))
    (hPa : ∀ z, AnalyticAt ℝ P (ContinuousMap.const PathDomain z))
    {α : ℝ → E} (hc : ContinuousOn α (Ici 0))
    (hd : ∀ t ≥ 0, HasDerivWithinAt α (F (α t)) (Ici 0) t) :
    ∃ β : ℝ → E, AnalyticAt ℝ β 0 ∧ β 0 = α 0 ∧
      α =ᶠ[𝓝[Ici 0] 0] β ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt β (F (β t)) t := by
  obtain ⟨β, hβ₀, δ, hδ, hβ⟩ := (hF (α 0)).exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  have hβd (t : ℝ) (ht : t ∈ Ioo (-δ) δ) : HasDerivAt β (F (β t)) t := by
    simpa only [zero_sub, zero_add] using hβ t (by simpa using ht)
  let T : ℝ := δ / 2
  have hT : 0 < T := by dsimp [T]; linarith
  have hsub : Icc (0 : ℝ) T ⊆ Ioo (-δ) δ := by
    intro t ht
    dsimp [T] at ht
    constructor <;> linarith [ht.1, ht.2]
  have hcα : ContinuousOn α (Icc 0 T) := hc.mono (fun _ ht ↦ ht.1)
  have hcβ : ContinuousOn β (Icc 0 T) := HasDerivAt.continuousOn (fun t ht ↦ hβd t (hsub ht))
  let C : Set E := α '' Icc 0 T ∪ β '' Icc 0 T
  have hC : IsCompact C := (isCompact_Icc.image_of_continuousOn hcα).union
    (isCompact_Icc.image_of_continuousOn hcβ)
  have hlocal : LocallyLipschitzOn C F := by
    intro z _
    obtain ⟨K, S, hS, hLip⟩ := (hF z).exists_lipschitzOnWith
    exact ⟨K, S, mem_nhdsWithin_of_mem_nhds hS, hLip⟩
  obtain ⟨K, hLip⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hC hlocal
  have heq := ODE_solution_unique_of_mem_Icc_right (v := fun _ ↦ F) (s := fun _ ↦ C)
    (fun _ _ ↦ hLip) hcα
    (fun t ht ↦ (hd t ht.1).mono (fun y hy ↦ ht.1.trans hy))
    (fun t ht ↦ Or.inl ⟨t, ⟨ht.1, ht.2.le⟩, rfl⟩) hcβ
    (fun t ht ↦ (hβd t (hsub ⟨ht.1, ht.2.le⟩)).hasDerivWithinAt)
    (fun t ht ↦ Or.inr ⟨t, ⟨ht.1, ht.2.le⟩, rfl⟩) hβ₀.symm
  have hβnear : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt β (F (β t)) t :=
    Filter.eventually_of_mem (Ioo_mem_nhds (by linarith) hδ) (fun t ht ↦ hβd t ht)
  refine ⟨β, analyticAt_of_local_lifted_field P (Eventually.of_forall hP) (hPa _) hβnear,
    hβ₀, ?_, hβnear⟩
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ u : ℝ in 𝓝 0, u < T from Iio_mem_nhds hT).filter_mono nhdsWithin_le_nhds] with t ht htT
  exact heq ⟨ht, htT.le⟩

end
end krylov.AnalyticTools
