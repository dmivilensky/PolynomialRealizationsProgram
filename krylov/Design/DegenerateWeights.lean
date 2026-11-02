import krylov.Design.MixedDesignTheorem

/-!
Article: main_krylov, thm:B and apC:lem:natoms, zero-weight boundary cases.
Use: complete the prescribed-atom equality for every nonnegative weight
vector, including an empty criterion and the all-zero objective.
Source: the actual finite atom-extension theorem and zero finite sums.
-/

namespace krylov.Design
noncomputable section
open MeasureTheory Set jacobi.Finite
open scoped BigOperators

/-- A genuine physical one-point probability design at the lower endpoint.
Article: main_krylov, thm:B, the degenerate objective. -/
def endpointDesign (I : chebyshev1.SpectralInterval) : DiscreteMeasure 1 where
  node _ := I.mu
  distinct _ _ _ := Subsingleton.elim _ _
  weight _ := 1
  positive _ := zero_lt_one
  probability := by simp

/-- Every positive prescribed support size has a genuine positive distinct-atom design.
Article: main_krylov, apC:lem:natoms, nonemptiness also for the zero criterion.
Proof: extend the real one-point endpoint measure using the already proved atom-padding theorem. -/
theorem exists_atomicIntervalDesign (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 0 < N) :
    Nonempty (AtomicIntervalDesign I N) := by
  obtain ⟨Q, hQ, _⟩ := exists_exact_atoms_approximation I (endpointDesign I)
    (fun _ => ⟨le_rfl, I.mu_lt_L.le⟩) hN 0 (fun i => Fin.elim0 i)
    (fun i => Fin.elim0 i) (by norm_num : (0 : ℝ) ≤ 1) le_rfl
    (by norm_num : (0 : ℝ) < 1)
  exact ⟨⟨Q, hQ⟩⟩

/-- An all-zero nonnegative weight vector gives the actual zero objective at every measure.
Article: main_krylov, thm:B, including an empty weight vector. -/
theorem intervalObjective_zero_weights (I : chebyshev1.SpectralInterval) (D : ℕ)
    (w : Fin D → ℝ) (hw : ∀ i, w i = 0) (γ : ℝ) (ν : ProbabilityMeasure (Spectrum I)) :
    intervalObjective I D w γ ν = 0 := by
  simp only [intervalObjective, mixedObjective, hw, zero_mul, Finset.sum_const_zero]

/-- The original small-support attainment theorem admits all nonnegative weights, including the empty and zero criteria.
Article: main_krylov, thm:B, full existence scope.
Proof: use the true positive-weight result when possible; a genuine endpoint
probability maximizes the zero criterion and has at most one support point. -/
theorem intervalObjective_attains_small_support_all (I : chebyshev1.SpectralInterval)
    (D : ℕ) (w : Fin D → ℝ) (hw : ∀ i, 0 ≤ w i) {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ ≤ 1) :
    ∃ ν : ProbabilityMeasure (Spectrum I),
      (∀ η, intervalObjective I D w γ η ≤ intervalObjective I D w γ ν) ∧
      (ν : Measure (Spectrum I)).support.Finite ∧ (ν : Measure (Spectrum I)).support.ncard ≤ D+1 := by
  by_cases hp : ∃ j, 0 < w j
  · obtain ⟨j, hj⟩ := hp
    exact intervalObjective_attains_small_support I D w hw hγ₀ hγ₁ j hj
  · have hz (i : Fin D) : w i = 0 := le_antisymm (not_lt.mp (fun h => hp ⟨i, h⟩)) (hw i)
    let p : Spectrum I := ⟨I.mu, le_rfl, I.mu_lt_L.le⟩
    let ν := atomicProbability (endpointDesign I) (fun _ : Fin 1 => p)
    have hν : (ν : Measure (Spectrum I)) = Measure.dirac p := by
      simp [ν, atomicProbability, endpointDesign]
    have hs : (ν : Measure (Spectrum I)).support ⊆ {p} :=
      Measure.support_subset_of_isClosed isClosed_singleton (by simp [hν])
    refine ⟨ν, ?_, (finite_singleton p).subset hs, ?_⟩
    · intro η
      rw [intervalObjective_zero_weights I D w hz, intervalObjective_zero_weights I D w hz]
    · exact (Set.ncard_le_ncard hs (finite_singleton p)).trans (by simp)

/-- The full-measure and prescribed-atom suprema coincide also for every degenerate weight vector.
Article: main_krylov, apC:lem:natoms, its full stated nonnegative-weight scope.
Proof: apply the positive-weight theorem when a positive summand exists;
otherwise nonnegativity makes every actual criterion identically zero. -/
theorem atomicDesignValue_eq_optimalValue_all (I : chebyshev1.SpectralInterval) (D N : ℕ)
    (hN : D + 1 ≤ N) (w : Fin D → ℝ) (hw : ∀ i, 0 ≤ w i)
    {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ ≤ 1) :
    atomicDesignValue I N D w γ = optimalValue I D w γ := by
  by_cases hp : ∃ j, 0 < w j
  · obtain ⟨j, hj⟩ := hp
    exact atomicDesignValue_eq_optimalValue I D N hN w hw hγ₀ hγ₁ j hj
  · have hz (i : Fin D) : w i = 0 := le_antisymm (not_lt.mp (fun h => hp ⟨i, h⟩)) (hw i)
    let ν := atomicProbability (endpointDesign I)
      (fun _ : Fin 1 => (⟨I.mu, le_rfl, I.mu_lt_L.le⟩ : Spectrum I))
    have hzero (η : ProbabilityMeasure (Spectrum I)) : intervalObjective I D w γ η = 0 :=
      intervalObjective_zero_weights I D w hz γ η
    have hval : optimalValue I D w γ = 0 := by
      rw [optimalValue_eq_of_maximizer I D w γ ν (fun η => by rw [hzero η, hzero ν]), hzero ν]
    let := exists_atomicIntervalDesign I N (by omega)
    have hatomic : atomicDesignObjective I D w γ (N := N) = fun _ => 0 := by
      funext Q
      exact hzero _
    rw [hval, atomicDesignValue, hatomic]
    simp

end
end krylov.Design
