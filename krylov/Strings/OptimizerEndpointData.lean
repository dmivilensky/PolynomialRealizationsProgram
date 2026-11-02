import krylov.Strings.OptimizerQuadratures

/-!
Article: main_krylov, thm:value, endpoint feedback construction.
Use: obtain globally continuous quadrature data from the actually constructed
global endpoint orbit. A constant negative-time extension allows ordinary FTC
and inverse-function theorems, while preserving every positive-time orbit value.
Source: the proved global endpoint shooting theorem, with no orbit assumed.
-/

namespace krylov.Strings.OptimizerQuadratures
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

/-- Globally continuous data for the endpoint optimizer quadratures exist.
The forward LV equations and corridor come from the constructed separating
orbit, rather than from hypotheses on a hypothetical global optimizer.
-/
theorem exists_endpoint_data_with_graph :
    ∃ e : ℝ → ℝ,
      (∀ r ≥ 1, e r ∈ Icc (1 : ℝ) 3 ∧
        HasDerivAt e (krylov.LotkaVolterra.endpointGraphRate r (e r)) r) ∧
    ∃ s U : ℝ → ℝ, Continuous s ∧ Continuous U ∧ U 0 = 1 ∧
      (∀ t, 2 ≤ s t) ∧
      (∀ t > 0, HasDerivAt s (2 * s t * (s t - 1 - U t)) t ∧
        HasDerivAt U (U t * (s t + 1 - U t)) t) ∧
      (∀ t ≥ 0, U t + 1 < s t ∧ s t < U t + 3 ∧ s t ≤ 4 * U t ∧
        Real.exp (2 * t) ≤ U t) ∧ ∀ t ≥ 0, s t = U t + e (U t) := by
  obtain ⟨e, he, α, hU₀, hαg⟩ := krylov.LotkaVolterra.exists_global_endpoint_orbit_with_graph
  have hα (t : ℝ) (ht : 0 ≤ t) :
      HasDerivAt α (krylov.LotkaVolterra.vectorField 1 (α t)) t ∧
        (α t).2 + 1 < (α t).1 ∧ (α t).1 < (α t).2 + 3 ∧
        (α t).1 ≤ 4 * (α t).2 ∧ Real.exp (2 * t) ≤ (α t).2 := by
    obtain ⟨hd, hA, hB, hC, hD, _⟩ := hαg t ht
    exact ⟨hd, hA, hB, hC, hD⟩
  let s : ℝ → ℝ := fun t ↦ (α (max t 0)).1
  let U : ℝ → ℝ := fun t ↦ (α (max t 0)).2
  have hcα : ContinuousOn α (Ici 0) := fun t ht ↦ (hα t ht).1.continuousAt.continuousWithinAt
  have hc : Continuous (fun t : ℝ ↦ α (max t 0)) :=
    hcα.comp_continuous (continuous_id.max continuous_const) (fun t ↦ le_max_right t 0)
  have hs : Continuous s := hc.fst
  have hU : Continuous U := hc.snd
  have hUzero : U 0 = 1 := by simpa only [U, max_self] using hU₀
  have hs₂ (t : ℝ) : 2 ≤ s t := by
    have h := hα (max t 0) (le_max_right _ _)
    have he : 1 ≤ Real.exp (2 * max t 0) := Real.one_le_exp_iff.mpr (by positivity)
    change 2 ≤ (α (max t 0)).1
    linarith [h.2.1, h.2.2.2.2]
  refine ⟨e, he, s, U, hs, hU, hUzero, hs₂, ?_, ?_, ?_⟩
  · intro t ht
    have heq : (fun u : ℝ ↦ α (max u 0)) =ᶠ[𝓝 t] α := by
      filter_upwards [Ioi_mem_nhds ht] with u hu
      rw [max_eq_left hu.le]
    have hd := (hα t ht.le).1.congr_of_eventuallyEq heq
    have hsf := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hd
    have hUs := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hd
    change HasDerivAt (fun u ↦ (α (max u 0)).1)
      (krylov.LotkaVolterra.vectorField 1 (α t)).1 t at hsf
    change HasDerivAt (fun u ↦ (α (max u 0)).2)
      (krylov.LotkaVolterra.vectorField 1 (α t)).2 t at hUs
    change HasDerivAt s _ t ∧ HasDerivAt U _ t
    constructor
    · simpa only [krylov.LotkaVolterra.vectorField, krylov.LotkaVolterra.sRate, one_mul,
        s, U, max_eq_left ht.le] using hsf
    · simpa only [krylov.LotkaVolterra.vectorField, krylov.LotkaVolterra.uRate,
        s, U, max_eq_left ht.le] using hUs
  · intro t ht
    simpa only [s, U, max_eq_left ht] using (hα t ht).2
  · intro t ht
    simpa only [s, U, max_eq_left ht] using (hαg t ht).2.2.2.2.2

/-- The endpoint data with the graph witness discarded when only orbit
quadratures are needed. -/
theorem exists_endpoint_data :
    ∃ s U : ℝ → ℝ, Continuous s ∧ Continuous U ∧ U 0 = 1 ∧
      (∀ t, 2 ≤ s t) ∧
      (∀ t > 0, HasDerivAt s (2 * s t * (s t - 1 - U t)) t ∧
        HasDerivAt U (U t * (s t + 1 - U t)) t) ∧
      ∀ t ≥ 0, U t + 1 < s t ∧ s t < U t + 3 ∧ s t ≤ 4 * U t ∧
        Real.exp (2 * t) ≤ U t := by
  obtain ⟨_, _, s, U, hs, hU, hU₀, hs₂, hode, hc, _⟩ := exists_endpoint_data_with_graph
  exact ⟨s, U, hs, hU, hU₀, hs₂, hode, hc⟩

end
end krylov.Strings.OptimizerQuadratures
