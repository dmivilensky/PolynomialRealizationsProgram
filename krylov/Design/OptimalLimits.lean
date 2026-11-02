import krylov.Design.InfiniteFiniteValues
import krylov.Design.SechMaximumBounds
import Mathlib.Topology.Order.MonotoneConvergence

/-!
Article: main_krylov, thm:B, the uniform-budget infinite criterion and the
asymptotic interval immediately following the Chebyshev majorants.
Use: prove actual finite optimized values converge monotonically to the
actual all-degree supremum, and express the numerical asymptotic sandwich
uniformly over every physical interval of a given small positive spacing.
Source: nonnegative partial sums, monotone convergence of real suprema,
and the independently proved discrete maximum and sampled-sech limits.
-/

namespace krylov.Design
noncomputable section
open Real Filter MeasureTheory Set
open scoped Topology

/-- The actual finite uniform response is monotone in its degree budget.
Article: main_krylov, the finite truncations of Gamma*. -/
theorem uniformObjective_monotone (I : chebyshev1.SpectralInterval)
    (ν : ProbabilityMeasure (Spectrum I)) :
    Monotone (fun M : ℕ => intervalObjective I M (fun _ => 1) (1 / 2) ν) := by
  intro M N hMN
  simp only [uniformObjective_eq_partialSum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hMN)
    (fun _ _ _ => sqrt_nonneg _)

/-- The genuine optimized finite uniform responses increase with the degree budget.
Article: main_krylov, Gamma*_{n-1} as a monotone truncation. -/
theorem uniformOptimalValue_monotone (I : chebyshev1.SpectralInterval) :
    Monotone (fun M : ℕ => optimalValue I M (fun _ => 1) (1 / 2)) := by
  intro M N hMN
  have hne : (range (intervalObjective I M (fun _ => 1) (1 / 2))).Nonempty :=
    ⟨_, lobattoProbability I 0, rfl⟩
  apply csSup_le hne
  rintro _ ⟨ν, rfl⟩
  exact (uniformObjective_monotone I ν hMN).trans
    (intervalObjective_half_le_optimalValue I N (fun _ => 1) (fun _ => zero_le_one) ν)

/-- Finite optimized uniform responses converge to the genuine infinite optimized value.
Article: main_krylov, the precise limiting meaning of Gamma*_{1,1/2}.
The supremum and limit concern actual optimized measure objectives. -/
theorem uniformOptimalValue_tendsto_infinite (I : chebyshev1.SpectralInterval) :
    Tendsto (fun M : ℕ => optimalValue I M (fun _ => 1) (1 / 2)) atTop
      (𝓝 (infiniteHalfValue I)) := by
  rw [infiniteHalfValue_eq_finite_supremum]
  exact tendsto_atTop_ciSup (uniformOptimalValue_monotone I)
    ⟨infiniteHalfValue I, by rintro _ ⟨M, rfl⟩; exact uniformOptimalValue_le_infinite I M⟩

/-- The actual scaled all-degree optimum always lies below pi/2.
Article: main_krylov, the upper endpoint of the asymptotic Chebyshev interval. -/
theorem infiniteHalfValue_scaled_le_pi (I : chebyshev1.SpectralInterval) :
    designSpacing I * infiniteHalfValue I ≤ π / 2 :=
  (infiniteHalfValue_scaled_sandwich I).2.trans
    (sampledSech_scaled_bounds (designSpacing_pos I)).2

/-- At every sufficiently small positive spacing, every physical interval has the source's numerical lower bound.
Article: main_krylov, theta*Gamma* asymptotically in [0.66274,pi/2].
The lower bound is strict and the upper bound is exact at every spacing;
the quantified statement is uniform over all physical intervals. -/
theorem infiniteHalfValue_scaled_eventually :
    ∀ᶠ θ : ℝ in 𝓝[>] 0, ∀ I : chebyshev1.SpectralInterval, designSpacing I = θ →
      (66274 / 100000 : ℝ) < θ * infiniteHalfValue I ∧ θ * infiniteHalfValue I ≤ π / 2 := by
  have hl : (66274 / 100000 : ℝ) < sechProfile sechOptimizer := by
    have h := sechProfile_max_rational_bounds.1
    linarith
  filter_upwards [sechGridMaximum_tendsto.eventually (lt_mem_nhds hl)] with θ hθ I hI
  constructor
  · rw [← hI]
    exact hθ.trans_le (hI ▸ (infiniteHalfValue_scaled_sandwich I).1)
  · simpa only [hI] using infiniteHalfValue_scaled_le_pi I

end
end krylov.Design
