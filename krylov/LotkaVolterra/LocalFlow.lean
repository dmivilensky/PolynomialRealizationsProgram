import krylov.LotkaVolterra.Saddle
import Mathlib.Analysis.ODE.ExistUnique

/-!
Article: `main_krylov`, `apC:prop:LV` and `apC:prop:g1`.

Actual local integral curves of the concrete Lotka--Volterra field, together
with local uniqueness and persistence inside the positive physical quadrant.

Source: mathlib's Picard--Lindelöf existence theorem for `C¹` fields and its
Gronwall uniqueness theorem. Polynomial regularity is established in `Saddle`.
No separatrix or global continuation is assumed in these local results.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set Filter
open scoped Topology

/-- A curve solves precisely the displayed autonomous field at each point of
its indicated time domain. Values outside that domain carry no meaning. -/
def IsSolutionOn (γ : ℝ) (α : ℝ → ℝ × ℝ) (I : Set ℝ) : Prop :=
  ∀ t ∈ I, HasDerivAt α (vectorField γ (α t)) t

theorem isOpen_positiveQuadrant : IsOpen positiveQuadrant := by
  change IsOpen {z : ℝ × ℝ | 0 < z.1 ∧ 0 < z.2}
  exact isOpen_lt continuous_const continuous_fst |>.inter
    (isOpen_lt continuous_const continuous_snd)

/-- Local existence is valid for every real parameter, including the singular
endpoint `γ = 1`. -/
theorem exists_local_solution (γ t₀ : ℝ) (z₀ : ℝ × ℝ) :
    ∃ α : ℝ → ℝ × ℝ, α t₀ = z₀ ∧ ∃ ε > 0,
      IsSolutionOn γ α (Ioo (t₀ - ε) (t₀ + ε)) := by
  exact (contDiff_vectorField γ 1).contDiffAt
    |>.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀

/-- A genuine local flow with continuous dependence on the initial point and
time. This is the input needed for openness of finite-time entrance/exit
conditions in the separating-orbit construction. -/
theorem exists_continuous_local_flow (γ t₀ : ℝ) (z₀ : ℝ × ℝ) :
    ∃ r > 0, ∃ ε > 0, ∃ Φ : (ℝ × ℝ) × ℝ → ℝ × ℝ,
      ContinuousOn Φ (Metric.closedBall z₀ r ×ˢ Icc (t₀ - ε) (t₀ + ε)) ∧
      ∀ z ∈ Metric.closedBall z₀ r, Φ (z, t₀) = z ∧
        IsSolutionOn γ (fun t ↦ Φ (z, t)) (Ioo (t₀ - ε) (t₀ + ε)) := by
  obtain ⟨ε, hε, a, r, L, K, hr, hPL⟩ :=
    IsPicardLindelof.of_contDiffAt_one (contDiff_vectorField γ 1).contDiffAt (x₀ := z₀)
  obtain ⟨Φ, hΦ, hc⟩ := (hPL t₀).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  refine ⟨r, hr, ε, hε, Φ, hc, fun z hz ↦ ⟨(hΦ z hz).1, ?_⟩⟩
  intro t ht
  exact ((hΦ z hz).2 t (Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

/-- Any existing solution starting in `Q` remains in `Q` on a sufficiently
small two-sided time interval. This is persistence of the actual curve,
rather than a sign calculation on the vector field. -/
theorem solution_eventually_positive {γ t₀ : ℝ} {α : ℝ → ℝ × ℝ}
    (hα : HasDerivAt α (vectorField γ (α t₀)) t₀)
    (hpos : α t₀ ∈ positiveQuadrant) :
    ∀ᶠ t in 𝓝 t₀, α t ∈ positiveQuadrant :=
  hα.continuousAt.preimage_mem_nhds (isOpen_positiveQuadrant.mem_nhds hpos)

/-- Positive initial data admit an actual local positive orbit. -/
theorem exists_local_positive_solution (γ t₀ : ℝ) {z₀ : ℝ × ℝ}
    (hz₀ : z₀ ∈ positiveQuadrant) :
    ∃ α : ℝ → ℝ × ℝ, α t₀ = z₀ ∧ ∃ ε > 0,
      IsSolutionOn γ α (Ioo (t₀ - ε) (t₀ + ε)) ∧
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), α t ∈ positiveQuadrant := by
  obtain ⟨α, hα₀, ε, hε, hα⟩ := exists_local_solution γ t₀ z₀
  have ht₀ : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := by constructor <;> linarith
  have hp := solution_eventually_positive (hα t₀ ht₀) (hα₀ ▸ hz₀)
  obtain ⟨δ, hδ, hδp⟩ := Metric.eventually_nhds_iff.mp hp
  refine ⟨α, hα₀, min ε δ, lt_min hε hδ, ?_, ?_⟩
  · intro t ht
    rcases ht with ⟨htlo, hthi⟩
    exact hα t ⟨by linarith [min_le_left ε δ], by linarith [min_le_left ε δ]⟩
  · intro t ht
    rcases ht with ⟨htlo, hthi⟩
    apply hδp
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [min_le_right ε δ]

/-- Germ uniqueness for any two actual solutions through the same initial
point. Local Lipschitz continuity is derived from the polynomial field, not
postulated as an additional hypothesis. -/
theorem local_solution_unique {γ t₀ : ℝ} {α β : ℝ → ℝ × ℝ}
    (hα : ∀ᶠ t in 𝓝 t₀, HasDerivAt α (vectorField γ (α t)) t)
    (hβ : ∀ᶠ t in 𝓝 t₀, HasDerivAt β (vectorField γ (β t)) t)
    (heq : α t₀ = β t₀) : α =ᶠ[𝓝 t₀] β := by
  obtain ⟨K, S, hS, hLip⟩ := (contDiff_vectorField γ 1).contDiffAt
    (x := α t₀) |>.exists_lipschitzOnWith
  have hα₀ := hα.self_of_nhds
  have hβ₀ := hβ.self_of_nhds
  have hαS : ∀ᶠ t in 𝓝 t₀, α t ∈ S := hα₀.continuousAt.preimage_mem_nhds hS
  have hβS : ∀ᶠ t in 𝓝 t₀, β t ∈ S :=
    hβ₀.continuousAt.preimage_mem_nhds (heq ▸ hS)
  exact ODE_solution_unique_of_eventually (v := fun _ ↦ vectorField γ)
    (s := fun _ ↦ S) (Eventually.of_forall fun _ ↦ hLip)
    (hα.and hαS) (hβ.and hβS) heq

/-- Equality as curves on an actual neighborhood follows for two solutions
defined on possibly different open time intervals. -/
theorem local_solution_unique_on_intervals {γ t₀ ε δ : ℝ}
    {α β : ℝ → ℝ × ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hα : IsSolutionOn γ α (Ioo (t₀ - ε) (t₀ + ε)))
    (hβ : IsSolutionOn γ β (Ioo (t₀ - δ) (t₀ + δ)))
    (heq : α t₀ = β t₀) : α =ᶠ[𝓝 t₀] β := by
  apply local_solution_unique (heq := heq)
  · exact Filter.eventually_of_mem (Ioo_mem_nhds (by linarith) (by linarith)) hα
  · exact Filter.eventually_of_mem (Ioo_mem_nhds (by linarith) (by linarith)) hβ

/-- Local uniqueness propagates across any connected open interval of
existence. This avoids imposing a spurious global Lipschitz bound on the
quadratic vector field. -/
theorem solution_unique_on_interval {γ l r t₀ : ℝ} {α β : ℝ → ℝ × ℝ}
    (hα : IsSolutionOn γ α (Ioo l r)) (hβ : IsSolutionOn γ β (Ioo l r))
    (ht₀ : t₀ ∈ Ioo l r) (heq : α t₀ = β t₀) : EqOn α β (Ioo l r) := by
  let C : Set ℝ := {t | t ∈ Ioo l r ∧ α t = β t}
  let D : Set ℝ := {t | t ∈ Ioo l r ∧ α t ≠ β t}
  have hC : IsOpen C := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have hn := isOpen_Ioo.mem_nhds ht.1
    have hl := local_solution_unique
      (Filter.eventually_of_mem hn hα) (Filter.eventually_of_mem hn hβ) ht.2
    exact Filter.inter_mem hn hl
  have hD : IsOpen D := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have hn := isOpen_Ioo.mem_nhds ht.1
    have hc := (hα t ht.1).continuousAt.prodMk (hβ t ht.1).continuousAt
    have hne : ∀ᶠ u in 𝓝 t, α u ≠ β u := hc.preimage_mem_nhds
      ((isOpen_ne_fun continuous_fst continuous_snd).mem_nhds ht.2)
    exact Filter.inter_mem hn hne
  have hdis : Disjoint C D := by
    rw [Set.disjoint_left]
    intro t ht ht'
    exact ht'.2 ht.2
  have hcover : Ioo l r ⊆ C ∪ D := by
    intro t ht
    by_cases he : α t = β t
    · exact Or.inl ⟨ht, he⟩
    · exact Or.inr ⟨ht, he⟩
  have hsub := isPreconnected_Ioo.subset_left_of_subset_union hC hD hdis hcover
    ⟨t₀, ht₀, ht₀, heq⟩
  exact fun t ht ↦ (hsub ht).2

end
end krylov.LotkaVolterra
