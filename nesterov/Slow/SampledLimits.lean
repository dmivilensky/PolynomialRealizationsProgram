import nesterov.Slow.SpreadPerturbation
import nesterov.Slow.QueryNormalization

/-!
The uniform all-lag spread margin survives every convergent finite collection
of slow coefficients. The spectrum is selected before the small parameter.
-/
namespace nesterov.Slow
noncomputable section
open Filter Flow
open scoped Topology BigOperators

theorem sampled_program_forced_charge {θ y c : ℝ} (W : SpreadWitness θ y c)
    (hc : 0<c) (hb : 0≤θ-2*c)
    (G S : ℝ→Fin W.J→ℝ) (a : ℝ→ℝ)
    (hG : ∀ j,Tendsto (fun ε=>G ε j) (𝓝[>] (0:ℝ))
      (𝓝 (W.spectrum.frequency j^2-delta θ y c)))
    (hS : ∀ j,Tendsto (fun ε=>S ε j) (𝓝[>] (0:ℝ))
      (𝓝 ((θ-2*c)*W.spectrum.frequency j)))
    (ha : ∀ᶠ ε in 𝓝[>] (0:ℝ),0<a ε) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),
      FiniteProgram W.spectrum.weight (fun j=>ε*W.spectrum.frequency j)
        (fun j=>a ε*G ε j) (fun j=>a ε*S ε j) (-c*ε) (a ε*sampleCharge W.spectrum.weight W.spectrum.frequency (S ε) c) ∧
      |a ε*sampleCharge W.spectrum.weight W.spectrum.frequency (S ε) c|<∑ j,W.spectrum.weight j*(a ε*G ε j) := by
  obtain ⟨η,hη,hrobust⟩ := spread_robust W hc hb
  have hg (j : Fin W.J) : ∀ᶠ ε in 𝓝[>] (0:ℝ),
      |G ε j-(W.spectrum.frequency j^2-delta θ y c)|≤η := by
    filter_upwards [(Metric.tendsto_nhds.mp (hG j)) η hη] with ε hε
    simpa only [Real.dist_eq] using hε.le
  have hs (j : Fin W.J) : ∀ᶠ ε in 𝓝[>] (0:ℝ),
      |S ε j-(θ-2*c)*W.spectrum.frequency j|≤η := by
    filter_upwards [(Metric.tendsto_nhds.mp (hS j)) η hη] with ε hε
    simpa only [Real.dist_eq] using hε.le
  have hgs : ∀ᶠ ε in 𝓝[>] (0:ℝ),∀ j,|G ε j-(W.spectrum.frequency j^2-delta θ y c)|≤η :=
    Filter.eventually_all.mpr hg
  have hss : ∀ᶠ ε in 𝓝[>] (0:ℝ),∀ j,|S ε j-(θ-2*c)*W.spectrum.frequency j|≤η :=
    Filter.eventually_all.mpr hs
  filter_upwards [ha,hgs,hss,self_mem_nhdsWithin] with ε hapos hge hse hε
  obtain ⟨hlag,hmin⟩ := hrobust (G ε) (S ε) hge hse
  constructor
  · apply (sampled_scaled_program_iff hc hapos).mpr
    refine ⟨hmin.le,fun n hn=>hlag (n*ε) (mul_pos (Nat.cast_pos.mpr (by omega : 0<n)) hε)⟩
  · have hcharge : |sampleCharge W.spectrum.weight W.spectrum.frequency (S ε) c|<
        ∑ j,W.spectrum.weight j*G ε j := by
      rw [sampleCharge,abs_div,abs_neg,abs_of_pos hc]
      exact (div_lt_iff₀ hc).mpr (by simpa only [mul_comm] using hmin)
    rw [abs_mul,abs_of_pos hapos]
    have he : (∑ j,W.spectrum.weight j*(a ε*G ε j))=a ε*(∑ j,W.spectrum.weight j*G ε j) := by
      rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro j _;ring
    rw [he]
    exact mul_lt_mul_of_pos_left hcharge hapos


theorem sampled_program_of_limits {θ y c : ℝ} (W : SpreadWitness θ y c)
    (hc : 0<c) (hb : 0≤θ-2*c)
    (G S : ℝ→Fin W.J→ℝ) (a : ℝ→ℝ)
    (hG : ∀ j,Tendsto (fun ε=>G ε j) (𝓝[>] (0:ℝ))
      (𝓝 (W.spectrum.frequency j^2-delta θ y c)))
    (hS : ∀ j,Tendsto (fun ε=>S ε j) (𝓝[>] (0:ℝ))
      (𝓝 ((θ-2*c)*W.spectrum.frequency j)))
    (ha : ∀ᶠ ε in 𝓝[>] (0:ℝ),0<a ε) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),∃ C : ℝ,
      FiniteProgram W.spectrum.weight (fun j=>ε*W.spectrum.frequency j)
        (fun j=>a ε*G ε j) (fun j=>a ε*S ε j) (-c*ε) C ∧
      |C|<∑ j,W.spectrum.weight j*(a ε*G ε j) := by
  filter_upwards [sampled_program_forced_charge W hc hb G S a hG hS ha] with ε hε
  exact ⟨a ε*sampleCharge W.spectrum.weight W.spectrum.frequency (S ε) c,hε⟩

end
end nesterov.Slow
