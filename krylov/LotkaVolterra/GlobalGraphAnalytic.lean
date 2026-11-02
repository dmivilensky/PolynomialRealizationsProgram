import krylov.LotkaVolterra.GlobalChordUniqueness
import krylov.LotkaVolterra.AnalyticSaddleGraph

/-!
Article: `main_krylov`, `apC:prop:LV`, analyticity of the actual globally
constructed separating graph at the saddle.

The bounded global chord is matched to the analytic local chord by the
proved expanding-trajectory uniqueness theorem. Thus analytic regularity
is attached to the actual global graph, rather than to an unrelated local
solution of the singular equation.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set Filter
open scoped Topology

namespace SubcriticalGraph
variable {γ : ℝ} (G : SubcriticalGraph γ)

theorem rawChord_eq_analytic_chord (hγ : 0 < γ) (hγ₁ : γ < 1)
    {w : ℝ → ℝ}
    (hstrip : ∀ u ∈ Icc (-1 : ℝ) 1, w u ∈ Icc 0 γ)
    (hder : ∀ u ∈ Icc (-1 : ℝ) 1, u ≠ 0 →
      HasDerivAt w (saddleSlopeRate γ ((saddleU γ / 2) * u) (w u) / u) u) :
    ∀ u ∈ Icc (-1 : ℝ) 1, u ≠ 0 → G.rawChord u = w u :=
  bounded_saddle_chord_unique hγ hγ₁
    (fun _ hu hu₀ ↦ ⟨(G.rawChord_bounds hγ₁ hu hu₀).1.le,
      (G.rawChord_bounds hγ₁ hu hu₀).2.le⟩)
    (fun u hu _ ↦ hstrip u hu) (fun _ hu hu₀ ↦ G.rawChord_hasDerivAt hγ₁ hu hu₀) hder

theorem analyticAt_saddle (hγ : 0 < γ) (hγ₁ : γ < 1) :
    AnalyticAt ℝ G.σ (saddleU γ) := by
  obtain ⟨r, w, _, _, _, hwA, _, hwd⟩ := exists_analytic_saddle_chord hγ hγ₁
  have heq := G.rawChord_eq_analytic_chord hγ hγ₁
    (fun u hu ↦ ⟨(hwd u hu).1.1.le, (hwd u hu).1.2.le⟩)
    (fun u hu ↦ (hwd u hu).2)
  let c := saddleU γ / 2
  have hc : 0 < c := half_pos (saddleU_pos hγ₁)
  let T : ℝ → ℝ := fun U ↦ (saddleU γ - U) / c
  have hT₀ : T (saddleU γ) = 0 := by simp [T]
  have hTA : AnalyticAt ℝ T (saddleU γ) := by
    change AnalyticAt ℝ (fun U : ℝ ↦ (saddleU γ - U) * c⁻¹) (saddleU γ)
    exact (analyticAt_const.sub analyticAt_id).mul analyticAt_const
  have hwT : AnalyticAt ℝ (fun U ↦ w (T U)) (saddleU γ) := by
    have hwm : AnalyticAt ℝ w (T (saddleU γ)) := by simpa only [hT₀] using hwA
    exact hwm.comp hTA
  have hFA : AnalyticAt ℝ (fun U ↦ saddleS γ - (saddleU γ - U) * w (T U)) (saddleU γ) :=
    analyticAt_const.sub ((analyticAt_const.sub analyticAt_id).mul hwT)
  apply hFA.congr
  filter_upwards [Ioo_mem_nhds (show saddleU γ - c < saddleU γ by linarith)
    (show saddleU γ < saddleU γ + c by linarith)] with U hU
  by_cases hUF : U = saddleU γ
  · subst U
    simp [G.saddle]
  · have hu : T U ∈ Icc (-1 : ℝ) 1 := by
      dsimp [T]
      constructor
      · apply (le_div_iff₀ hc).mpr
        linarith [hU.2]
      · apply (div_le_iff₀ hc).mpr
        linarith [hU.1]
    have hu₀ : T U ≠ 0 := by
      dsimp [T]
      exact div_ne_zero (sub_ne_zero.mpr (Ne.symm hUF)) (ne_of_gt hc)
    have hch := heq (T U) hu hu₀
    have harg : c * T U = saddleU γ - U := by
      dsimp [T]
      field_simp
    have hback : saddleU γ - (saddleU γ / 2) * T U = U := by
      change saddleU γ - c * T U = U
      rw [harg]
      ring
    change (saddleS γ - G.σ (saddleU γ - (saddleU γ / 2) * T U)) /
      ((saddleU γ / 2) * T U) = w (T U) at hch
    rw [hback] at hch
    change (saddleS γ - G.σ U) / (c * T U) = w (T U) at hch
    rw [harg] at hch
    have hh := (div_eq_iff (sub_ne_zero.mpr (Ne.symm hUF))).mp hch
    nlinarith only [hh]

end SubcriticalGraph
end
end krylov.LotkaVolterra
