import krylov.LotkaVolterra.OrbitEstimates

/-!
Article: `main_krylov`, `apC:prop:LV`, exclusion of a backward limit at the
boundary sink `(0,1)`.

For this concrete field the relevant exclusion does not require a general
hyperbolic-sink theorem: the first coordinate strictly decreases whenever
`0 < s < 1` and `γ ≥ 0`. A positive orbit cannot therefore have first
coordinate tending to zero at minus infinity.

Source: direct one-dimensional comparison by the mean-value theorem.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set Filter
open scoped Topology

/-- Small positive control coordinates strictly decrease in forward time
for every nonnegative parameter and positive state coordinate. -/
theorem sRate_neg_of_lt_one {γ s U : ℝ} (hγ : 0 ≤ γ)
    (hs : 0 < s) (hs₁ : s < 1) (hU : 0 < U) : sRate γ s U < 0 := by
  have hm := mul_nonneg hγ hU.le
  exact mul_neg_of_pos_of_neg (by positivity) (by linarith)

/-- No positive orbit defined for arbitrarily negative times can approach
the `s = 0` axis backward in time. In particular this excludes `(0,1)` as
the backward limit of the bounded stable branch. -/
theorem no_positive_backward_limit_zero {γ b : ℝ} {α : ℝ → ℝ × ℝ}
    (hγ : 0 ≤ γ) (hα : IsSolutionOn γ α (Iio b))
    (hpos : ∀ t ∈ Iio b, α t ∈ positiveQuadrant) :
    ¬ Tendsto (fun t ↦ (α t).1) atBot (𝓝 0) := by
  intro hlim
  have hsmall : ∀ᶠ t in atBot, (α t).1 < 1 :=
    (tendsto_order.mp hlim).2 1 (by norm_num)
  obtain ⟨c, hc⟩ := eventually_atBot.mp hsmall
  let d := min c (b - 1)
  have hdb : d < b := by dsimp [d]; linarith [min_le_right c (b - 1)]
  have hdc : d ≤ c := min_le_left _ _
  have hanti : AntitoneOn (fun t ↦ (α t).1) (Iic d) := by
    apply StrictAntiOn.antitoneOn
    apply strictAntiOn_of_deriv_neg (convex_Iic d)
      (HasDerivAt.continuousOn (fun t ht ↦
        solution_s_hasDerivAt (hα t (lt_of_le_of_lt ht hdb))))
    intro t ht
    have htd : t ≤ d := mem_Iic.mp (interior_subset ht)
    have htb : t < b := lt_of_le_of_lt htd hdb
    rw [(solution_s_hasDerivAt (hα t htb)).deriv]
    exact sRate_neg_of_lt_one hγ (hpos t htb).1 (hc t (htd.trans hdc))
      (hpos t htb).2
  have hbound : ∀ᶠ t in atBot, (α d).1 ≤ (α t).1 := by
    filter_upwards [eventually_le_atBot d] with t ht
    exact hanti (mem_Iic.mpr ht) (mem_Iic.mpr le_rfl) ht
  have hzero : (α d).1 ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hlim hbound
  exact (not_lt_of_ge hzero) (hpos d hdb).1

end
end krylov.LotkaVolterra
