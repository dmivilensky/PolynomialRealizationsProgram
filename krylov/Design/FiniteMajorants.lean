import krylov.Design.HyperbolicDictionary
import krylov.Design.PrescribedAtoms

/-!
Article: main_krylov, the two Chebyshev majorants immediately following thm:B.
Use: state both bounds for the actual optimized mixed value Gamma*, retaining
all nonnegative and zero weights. The lower bound is witnessed by the actual
Lobatto design, while the upper bound holds for every probability measure.
Source: the proved sharp extrapolation design and compact-measure optimization.
-/

namespace krylov.Design
noncomputable section
open Real MeasureTheory Set
open scoped BigOperators

/-- The optimized mixed first-order response has the literal finite weighted sech majorant.
Article: main_krylov, the upper bound following thm:B. -/
theorem optimalValue_half_majorant (I : chebyshev1.SpectralInterval) (M : ℕ)
    (w : Fin M → ℝ) (hw : ∀ i, 0 ≤ w i) :
    optimalValue I M w (1 / 2) ≤ ∑ i, w i * jacobi.Young.sech ((i.val + 1 : ℝ) * designSpacing I) := by
  have hne : (range (intervalObjective I M w (1 / 2))).Nonempty := ⟨_, lobattoProbability I 0, rfl⟩
  apply csSup_le hne
  rintro _ ⟨ν, rfl⟩
  simpa only [epsilon_eq_sech, Nat.cast_add, Nat.cast_one] using
    intervalObjective_half_majorant I M w hw ν

/-- Every genuine measure is below the actual finite optimized response, including zero weights.
Article: main_krylov, Gamma* as a genuine full-measure optimum. -/
theorem intervalObjective_half_le_optimalValue (I : chebyshev1.SpectralInterval) (M : ℕ)
    (w : Fin M → ℝ) (hw : ∀ i, 0 ≤ w i) (ν : ProbabilityMeasure (Spectrum I)) :
    intervalObjective I M w (1 / 2) ν ≤ optimalValue I M w (1 / 2) := by
  have hbd : BddAbove (range (intervalObjective I M w (1 / 2))) := by
    refine ⟨∑ i, w i * I.epsilon (i.val + 1), ?_⟩
    rintro _ ⟨η, rfl⟩
    exact intervalObjective_half_majorant I M w hw η
  exact le_csSup hbd (mem_range_self ν)

/-- Each candidate prefix has the article's actual optimized lower bound.
Article: main_krylov, the lower bound following thm:B.
This holds for every candidate degree k, and in particular for every k<=M. -/
theorem optimalValue_half_lobatto_lower (I : chebyshev1.SpectralInterval) (M k : ℕ)
    (w : Fin M → ℝ) (hw : ∀ i, 0 ≤ w i) :
    jacobi.Young.sech ((k : ℝ) * designSpacing I) *
      ∑ i ∈ Finset.univ.filter (fun i : Fin M => i.val + 1 ≤ k), w i ≤
      optimalValue I M w (1 / 2) := by
  rw [← epsilon_eq_sech]
  exact (intervalObjective_half_lobatto_lower I M k w hw).trans
    (intervalObjective_half_le_optimalValue I M w hw _)

/-- The actual maximum of all finite prefix lower bounds is below Gamma*.
Article: main_krylov, the complete displayed Chebyshev lower majorant after thm:B.
The degree-zero candidate is identically zero, so the definition also covers M=0. -/
theorem finite_prefix_max_le_optimalValue (I : chebyshev1.SpectralInterval) (M : ℕ)
    (w : Fin M → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (Finset.range (M + 1)).sup' (by simp)
      (fun k => jacobi.Young.sech ((k : ℝ) * designSpacing I) *
        ∑ i ∈ Finset.univ.filter (fun i : Fin M => i.val + 1 ≤ k), w i) ≤
      optimalValue I M w (1 / 2) := by
  apply Finset.sup'_le
  intro k _
  exact optimalValue_half_lobatto_lower I M k w hw

end
end krylov.Design
