import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Article: main_krylov, thm:A, worst-reference supremum asymptotics.
Use: combine a genuine uniform quadratic upper estimate with actual local
near-extremizing reference paths, without compactness of the full reference set.
Source: the defining least-upper-bound property and the real order criterion
for convergence; no maximizer or common lower-path domain radius is assumed.
-/

namespace krylov.Stability
noncomputable section
open Filter Set Topology

/-- Actual feasible-value suprema converge after first-order scaling to the genuine supremum of their reference coefficients.
Use: Actual feasible-value suprema converge after first-order scaling to the genuine supremum of their reference coefficients.
Article: main_krylov, thm:A, worst-reference supremum asymptotics.
Proof: For a lower threshold choose one actual coefficient above it and its locally feasible convergent path. The uniform upper bound controls the true finite supremum; division by the actual positive scale and the real order convergence criterion give both limits. -/
theorem supremum_firstOrder (L : Set ℝ) (hL : L.Nonempty)
    (S : ℝ → Set ℝ) (hS : ∀ t, (S t).Nonempty) (C : ℝ)
    (hupper : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ v∈S t, v≤t*sSup L+C*t^2)
    (hlower : ∀ b∈L, ∃ f : ℝ → ℝ,
      Tendsto (fun t => f t/t) (𝓝[>] (0 : ℝ)) (𝓝 b) ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), f t∈S t) :
    Tendsto (fun t => sSup (S t)/t) (𝓝[>] (0 : ℝ)) (𝓝 (sSup L)) := by
  -- A separate actual near-extremizing path suffices for each lower threshold.
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨b,hb,hab⟩ := exists_lt_of_lt_csSup hL ha
    obtain ⟨f,hf,hmem⟩ := hlower b hb
    filter_upwards [hf.eventually (Ioi_mem_nhds hab),hmem,hupper,self_mem_nhdsWithin] with t ht hm hu hp
    exact ht.trans_le (div_le_div_of_nonneg_right (le_csSup ⟨_,hu⟩ hm) hp.le)
  · intro a ha
    have hlin : Tendsto (fun t : ℝ => sSup L+C*t) (𝓝[>] 0) (𝓝 (sSup L)) := by
      have hc : ContinuousAt (fun t : ℝ => sSup L+C*t) 0 := by fun_prop
      simpa only [mul_zero,add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
    filter_upwards [hlin.eventually (Iio_mem_nhds ha),hupper,self_mem_nhdsWithin] with t ht hu hp
    have hs := csSup_le (hS t) hu
    have hq : sSup (S t)/t≤sSup L+C*t := (div_le_iff₀ hp).mpr (by nlinarith [hs])
    exact hq.trans_lt ht
end
end krylov.Stability
