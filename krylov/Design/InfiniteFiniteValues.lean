import krylov.Design.InfiniteMajorants
import krylov.Design.FiniteMajorants

/-!
Article: main_krylov, Gamma* and its finite-budget truncations after thm:B.
Use: connect the actual all-degree measure objective and the finite optimized
criteria, proving the infinite value is exactly their supremum. Convergence
is derived from genuine summable Christoffel majorization.
Source: finite partial sums, the already proved summability, and real suprema.
-/

namespace krylov.Design
noncomputable section
open Real Filter MeasureTheory Set
open scoped Topology BigOperators

/-- Uniform finite mixed response is exactly the genuine initial partial sum of the infinite response.
Article: main_krylov, Gamma*_{n-1} versus Gamma*. -/
theorem uniformObjective_eq_partialSum (I : chebyshev1.SpectralInterval) (M : ℕ)
    (ν : ProbabilityMeasure (Spectrum I)) :
    intervalObjective I M (fun _ => 1) (1 / 2) ν =
      ∑ n ∈ Finset.range M, sqrt (christoffel (n + 1) 0 (spectralCoordinate I) ν) := by
  unfold intervalObjective mixedObjective
  simp only [one_mul, ← Real.sqrt_eq_rpow]
  exact Fin.sum_univ_eq_sum_range (fun n : ℕ => sqrt (christoffel (n + 1) 0 (spectralCoordinate I) ν)) M

/-- Finite uniform responses converge to the actual infinite response at every genuine probability measure.
Article: main_krylov, the infinite-degree objective. -/
theorem uniformObjective_tendsto_infinite (I : chebyshev1.SpectralInterval)
    (ν : ProbabilityMeasure (Spectrum I)) :
    Tendsto (fun M : ℕ => intervalObjective I M (fun _ => 1) (1 / 2) ν) atTop
      (𝓝 (infiniteHalfObjective I ν)) := by
  simp only [uniformObjective_eq_partialSum]
  exact (infiniteHalfObjective_summable I ν).hasSum.tendsto_sum_nat

/-- Every finite uniform response lies below the actual all-degree response of the same measure.
Article: main_krylov, monotone budget truncation. -/
theorem uniformObjective_le_infinite (I : chebyshev1.SpectralInterval) (M : ℕ)
    (ν : ProbabilityMeasure (Spectrum I)) :
    intervalObjective I M (fun _ => 1) (1 / 2) ν ≤ infiniteHalfObjective I ν := by
  rw [uniformObjective_eq_partialSum]
  exact Summable.sum_le_tsum (Finset.range M) (fun _ _ => sqrt_nonneg _)
    (infiniteHalfObjective_summable I ν)

/-- Optimizing a finite uniform budget gives a value below the genuine infinite optimum.
Article: main_krylov, Gamma*_{n-1}<=Gamma*. -/
theorem uniformOptimalValue_le_infinite (I : chebyshev1.SpectralInterval) (M : ℕ) :
    optimalValue I M (fun _ => 1) (1 / 2) ≤ infiniteHalfValue I := by
  have hne : (range (intervalObjective I M (fun _ => 1) (1 / 2))).Nonempty :=
    ⟨_, lobattoProbability I 0, rfl⟩
  apply csSup_le hne
  rintro _ ⟨ν, rfl⟩
  exact (uniformObjective_le_infinite I M ν).trans (infiniteHalfObjective_le_value I ν)

/-- The actual infinite optimum is exactly the supremum of the actual finite uniform optima.
Article: main_krylov, the precise infinite-budget meaning of Gamma*.
Proof: each finite criterion is below the all-degree response; conversely,
each genuine response is a limit of finite criteria bounded by their optimized supremum. -/
theorem infiniteHalfValue_eq_finite_supremum (I : chebyshev1.SpectralInterval) :
    infiniteHalfValue I = sSup (range (fun M : ℕ => optimalValue I M (fun _ => 1) (1 / 2))) := by
  let V := sSup (range (fun M : ℕ => optimalValue I M (fun _ => 1) (1 / 2)))
  have hbd : BddAbove (range (fun M : ℕ => optimalValue I M (fun _ => 1) (1 / 2))) :=
    ⟨infiniteHalfValue I, by rintro _ ⟨M, rfl⟩; exact uniformOptimalValue_le_infinite I M⟩
  have hfinite (M : ℕ) : optimalValue I M (fun _ => 1) (1 / 2) ≤ V :=
    le_csSup hbd (mem_range_self M)
  apply le_antisymm
  · change sSup (range (infiniteHalfObjective I)) ≤ V
    have hne : (range (infiniteHalfObjective I)).Nonempty := ⟨_, lobattoProbability I 0, rfl⟩
    refine csSup_le hne ?_
    rintro _ ⟨ν, rfl⟩
    apply le_of_tendsto (uniformObjective_tendsto_infinite I ν)
    exact Filter.Eventually.of_forall (fun M =>
      (intervalObjective_half_le_optimalValue I M (fun _ => 1) (fun _ => zero_le_one) ν).trans (hfinite M))
  · exact csSup_le (range_nonempty _) (by rintro _ ⟨M, rfl⟩; exact uniformOptimalValue_le_infinite I M)

end
end krylov.Design
