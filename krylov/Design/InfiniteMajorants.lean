import krylov.Design.HyperbolicDictionary
import krylov.Design.SechGridLimit

/-!
Article: main_krylov, the infinite-budget Chebyshev bounds after thm:B.
Use: define the actual infinite mixed objective on all physical probability
measures; prove genuine convergence and the source's lower/upper sandwich,
using the attained integer maximum and the actual hyperbolic sum.
Source: the independently proved finite design extremum, degree monotonicity,
and summable Chebyshev majorization. No infinite-objective regularity is assumed.
-/

namespace krylov.Design
noncomputable section
open Real Filter MeasureTheory Set jacobi.Young
open scoped Topology BigOperators

/-- The actual all-degree first-order response of one physical probability measure.
Article: main_krylov, Gamma* for uniform budgets and gamma=1/2. -/
def infiniteHalfObjective (I : chebyshev1.SpectralInterval) (ν : ProbabilityMeasure (Spectrum I)) : ℝ :=
  ∑' n : ℕ, sqrt (christoffel (n + 1) 0 (spectralCoordinate I) ν)

/-- The true all-probability-measure optimum of the actual infinite response.
Article: main_krylov, Gamma*=Gamma*_{1,1/2}. -/
def infiniteHalfValue (I : chebyshev1.SpectralInterval) : ℝ :=
  sSup (range (infiniteHalfObjective I))

/-- Every genuine infinite response converges, uniformly dominated by the actual sech samples.
Article: main_krylov, the infinite-budget Chebyshev upper majorant. -/
theorem infiniteHalfObjective_summable (I : chebyshev1.SpectralInterval)
    (ν : ProbabilityMeasure (Spectrum I)) :
    Summable (fun n : ℕ => sqrt (christoffel (n + 1) 0 (spectralCoordinate I) ν)) := by
  apply Summable.of_nonneg_of_le (fun n => sqrt_nonneg _) _
    (sampledSech_summable (designSpacing_pos I))
  intro n
  simpa only [epsilon_eq_sech, Nat.cast_add, Nat.cast_one] using
    sqrt_christoffel_le_chebyshev I (n + 1) ν

/-- The actual infinite response obeys the actual infinite sech majorant.
Article: main_krylov, the infinite-budget upper bound following thm:B. -/
theorem infiniteHalfObjective_le_majorant (I : chebyshev1.SpectralInterval)
    (ν : ProbabilityMeasure (Spectrum I)) :
    infiniteHalfObjective I ν ≤ sampledSech (designSpacing I) := by
  apply (infiniteHalfObjective_summable I ν).tsum_le_tsum _
    (sampledSech_summable (designSpacing_pos I))
  intro n
  simpa only [epsilon_eq_sech, Nat.cast_add, Nat.cast_one] using
    sqrt_christoffel_le_chebyshev I (n + 1) ν

/-- The genuine infinite optimum is finite and has the source's sharp explicit upper majorant.
Article: main_krylov, Gamma*<=sum_m sech(m*theta). -/
theorem infiniteHalfValue_le_majorant (I : chebyshev1.SpectralInterval) :
    infiniteHalfValue I ≤ sampledSech (designSpacing I) := by
  have hne : (range (infiniteHalfObjective I)).Nonempty :=
    ⟨_, lobattoProbability I 0, rfl⟩
  exact csSup_le hne (by
    rintro _ ⟨ν, rfl⟩
    exact infiniteHalfObjective_le_majorant I ν)

/-- Every actual probability response lies below the true infinite optimum.
Article: main_krylov, Gamma* as an all-measures supremum. -/
theorem infiniteHalfObjective_le_value (I : chebyshev1.SpectralInterval)
    (ν : ProbabilityMeasure (Spectrum I)) : infiniteHalfObjective I ν ≤ infiniteHalfValue I :=
  le_csSup ⟨sampledSech (designSpacing I), by
    rintro _ ⟨η, rfl⟩
    exact infiniteHalfObjective_le_majorant I η⟩ (mem_range_self ν)

/-- The degree-m actual Lobatto design gives the source's m*sech(m*theta) lower bound.
Article: main_krylov, the infinite-budget lower Chebyshev majorant. -/
theorem lobatto_infiniteHalf_lower (I : chebyshev1.SpectralInterval) (m : ℕ) :
    (m : ℝ) * sech ((m : ℝ) * designSpacing I) ≤
      infiniteHalfObjective I (lobattoProbability I m) := by
  have h := intervalObjective_half_lobatto_lower I m m (fun _ => 1) (fun _ => zero_le_one)
  have hf : Finset.univ.filter (fun i : Fin m => i.val + 1 ≤ m) = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro i _
    exact Nat.succ_le_iff.mpr i.isLt
  rw [hf] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    epsilon_eq_sech] at h
  apply (mul_comm _ _).trans_le (h.trans _)
  unfold intervalObjective mixedObjective infiniteHalfObjective
  simp only [one_mul, ← Real.sqrt_eq_rpow]
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ =>
    sqrt (christoffel (n + 1) 0 (spectralCoordinate I) (lobattoProbability I m)))]
  exact Summable.sum_le_tsum (Finset.range m) (fun _ _ => sqrt_nonneg _)
    (infiniteHalfObjective_summable I _)

/-- The genuine source integer maximum is below the true infinite-measure optimum.
Article: main_krylov, max_m m*sech(m*theta)<=Gamma*. -/
theorem discreteSechMaximum_le_infiniteHalfValue (I : chebyshev1.SpectralInterval) :
    discreteSechMaximum (designSpacing I) ≤ infiniteHalfValue I := by
  apply csSup_le (range_nonempty _)
  rintro _ ⟨n, rfl⟩
  have h := (lobatto_infiniteHalf_lower I (n + 1)).trans (infiniteHalfObjective_le_value I _)
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-- The source's full actual all-measures asymptotic sandwich at each positive physical interval.
Article: main_krylov, theta*Gamma* asymptotically between 0.66274 and pi/2.
Both endpoints here are genuine maxima/sums already proved to have the source limits. -/
theorem infiniteHalfValue_scaled_sandwich (I : chebyshev1.SpectralInterval) :
    sechGridMaximum (designSpacing I) ≤ designSpacing I * infiniteHalfValue I ∧
      designSpacing I * infiniteHalfValue I ≤ designSpacing I * sampledSech (designSpacing I) := by
  constructor
  · rw [← (discreteSechMaximum_attained (designSpacing_pos I)).2]
    exact mul_le_mul_of_nonneg_left (discreteSechMaximum_le_infiniteHalfValue I) (designSpacing_pos I).le
  · exact mul_le_mul_of_nonneg_left (infiniteHalfValue_le_majorant I) (designSpacing_pos I).le

end
end krylov.Design
