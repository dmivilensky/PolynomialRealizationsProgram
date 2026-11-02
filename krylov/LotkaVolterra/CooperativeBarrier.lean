import krylov.LotkaVolterra.Barrier

/-!
Article: main_krylov, apC:prop:LV, closed upper-wedge invariance.
Use: preserve nonnegative coordinates for an actual two-dimensional linear
system with nonnegative off-diagonal coefficients. A positive exponential
perturbation makes both boundaries strict; then the perturbation tends to zero.
Source: the standard cooperative-system barrier argument and first contact.
-/

namespace krylov.LotkaVolterra
noncomputable section
open Set Filter
open scoped Topology

/-- Closed quadrant invariance for an actual cooperative two-component
system. Only a finite row-sum bound is needed on the existing time interval. -/
theorem pair_nonnegative_cooperative {a b c d f g : ℝ → ℝ} {t₀ T K : ℝ}
    (hT : t₀ ≤ T)
    (hf : ∀ t ∈ Icc t₀ T, HasDerivAt f (a t * f t + b t * g t) t)
    (hg : ∀ t ∈ Icc t₀ T, HasDerivAt g (c t * f t + d t * g t) t)
    (hb : ∀ t ∈ Icc t₀ T, 0 ≤ b t) (hc : ∀ t ∈ Icc t₀ T, 0 ≤ c t)
    (hK : ∀ t ∈ Icc t₀ T, a t + b t ≤ K ∧ c t + d t ≤ K)
    (hf₀ : 0 ≤ f t₀) (hg₀ : 0 ≤ g t₀) : 0 ≤ f T ∧ 0 ≤ g T := by
  have heps (ε : ℝ) (hε : 0 < ε) :
      0 < f T + ε * Real.exp ((K + 1) * (T - t₀)) ∧
      0 < g T + ε * Real.exp ((K + 1) * (T - t₀)) := by
    let E : ℝ → ℝ := fun t ↦ ε * Real.exp ((K + 1) * (t - t₀))
    have hE (t : ℝ) : 0 < E t := mul_pos hε (Real.exp_pos _)
    have hdE (t : ℝ) : HasDerivAt E ((K + 1) * E t) t := by
      convert! (((hasDerivAt_id t).sub_const t₀).const_mul (K + 1)).exp.const_mul ε using 1
      dsimp [E]
      ring
    apply pair_positive_invariant hT
      (fun t ht ↦ (hf t ht).add (hdE t)) (fun t ht ↦ (hg t ht).add (hdE t))
      (by exact add_pos_of_nonneg_of_pos hf₀ (hE t₀))
      (by exact add_pos_of_nonneg_of_pos hg₀ (hE t₀))
    · intro t ht hzero hnonneg
      change f t + E t = 0 at hzero
      have heq : f t = -E t := by linarith
      rw [heq]
      have hmul := mul_nonneg (hb t ht) hnonneg
      have hsum := mul_nonneg (sub_nonneg.mpr (hK t ht).1) (hE t).le
      dsimp only [Pi.add_apply] at hmul
      nlinarith [hE t]
    · intro t ht hzero hpos
      change g t + E t = 0 at hzero
      have heq : g t = -E t := by linarith
      rw [heq]
      have hmul := mul_nonneg (hc t ht) hpos.le
      have hsum := mul_nonneg (sub_nonneg.mpr (hK t ht).2) (hE t).le
      dsimp only [Pi.add_apply] at hmul
      nlinarith [hE t]
  have hlim : Tendsto (fun ε : ℝ ↦ ε * Real.exp ((K + 1) * (T - t₀))) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((tendsto_id : Tendsto (fun ε : ℝ ↦ ε) (𝓝 0) (𝓝 0)).mono_left nhdsWithin_le_nhds).mul_const
      (Real.exp ((K + 1) * (T - t₀)))
  constructor
  · have hn : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 ≤ f T + ε * Real.exp ((K + 1) * (T - t₀)) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (heps ε hε).1.le
    have hh : 0 ≤ f T + 0 := ge_of_tendsto (tendsto_const_nhds.add hlim) hn
    simpa using hh
  · have hn : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 ≤ g T + ε * Real.exp ((K + 1) * (T - t₀)) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (heps ε hε).2.le
    have hh : 0 ≤ g T + 0 := ge_of_tendsto (tendsto_const_nhds.add hlim) hn
    simpa using hh

end
end krylov.LotkaVolterra
