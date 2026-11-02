import krylov.Design.InverseInformationDerivative

/-!
Article: main_krylov, thm:B, actual probability-measure segments and their moments.
Use: retain the original measure domain while applying finite matrix calculus.
Source: linearity of moment integration and positivity of monomial Gram forms.
-/

namespace krylov.Design
noncomputable section
open Polynomial MeasureTheory Matrix Set
open scoped BigOperators NNReal

/-- Every genuine moment matrix is positive semidefinite, including singular measures.
Article: main_krylov, thm:B. -/
theorem momentGram_posSemidef (I : chebyshev1.SpectralInterval) (m : ℕ)
    (ν : ProbabilityMeasure (Spectrum I)) : (momentGram I m ν).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.isHermitian_iff_isSymm.mpr (momentGram_isSymm I m ν))
  intro a
  rw [star_trivial, ← polynomialEnergy_eq_momentGram]
  exact polynomialEnergy_nonneg _ _ _

/-- Moments are affine under the actual probability mixture.
Article: main_krylov, thm:B. -/
theorem momentGram_mixture (I : chebyshev1.SpectralInterval) (m : ℕ)
    (ν η : ProbabilityMeasure (Spectrum I)) (a b : ℝ≥0) (hab : a + b = 1) :
    momentGram I m (mixture ν η a b hab) = (a : ℝ) • momentGram I m ν + (b : ℝ) • momentGram I m η := by
  ext i j
  have hi (μ : Measure (Spectrum I)) [IsFiniteMeasure μ] :
      Integrable (fun t : Spectrum I => t.val ^ i.val * t.val ^ j.val) μ :=
    (by fun_prop : Continuous (fun t : Spectrum I => t.val ^ i.val * t.val ^ j.val)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ t : Spectrum I, t.val ^ i.val * t.val ^ j.val
    ∂(a • (ν : Measure (Spectrum I)) + b • (η : Measure (Spectrum I)))) = _
  rw [integral_add_measure (hi _) (hi _), integral_smul_nnreal_measure,
    integral_smul_nnreal_measure]
  rfl

/-- The actual measure segment, extended by its initial endpoint outside the unit interval.
The extension permits ordinary real-variable derivative notation; all conclusions
use the one-sided derivative within the genuine probability segment.
Article: main_krylov, thm:B. -/
def measureSegment {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (ν η : ProbabilityMeasure X) (s : ℝ) : ProbabilityMeasure X :=
  if h : s ∈ Icc (0 : ℝ) 1 then
    mixture ν η (1 - s).toNNReal s.toNNReal (by
      ext
      rw [NNReal.coe_add, Real.coe_toNNReal _ (by linarith [h.2]), Real.coe_toNNReal _ h.1]
      norm_num)
  else ν

/-- The zero mixing parameter is exactly the original measure.
Article: main_krylov, thm:B. -/
theorem measureSegment_zero {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (ν η : ProbabilityMeasure X) : measureSegment ν η 0 = ν := by
  apply Subtype.ext
  simp only [measureSegment, show (0 : ℝ) ∈ Icc 0 1 by norm_num, dite_true]
  change (1 - (0 : ℝ)).toNNReal • (ν : Measure X) + (0 : ℝ).toNNReal • (η : Measure X) = _
  simp

/-- The original probability segment has exactly the affine moment path used by inverse calculus.
Article: main_krylov, thm:B. -/
theorem momentGram_measureSegment (I : chebyshev1.SpectralInterval) (m : ℕ)
    (ν η : ProbabilityMeasure (Spectrum I)) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    momentGram I m (measureSegment ν η s) = momentGram I m ν + s • (momentGram I m η - momentGram I m ν) := by
  rw [measureSegment, dite_eq_left hs, momentGram_mixture,
    Real.coe_toNNReal _ (by linarith [hs.2]), Real.coe_toNNReal _ hs.1]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring

/-- A nonsingular initial design remains nonsingular along every proper probability mixture.
Article: main_krylov, thm:B.
Proof: retain a strictly positive multiple of its positive Gram matrix and add a positive semidefinite Gram matrix. -/
theorem momentGram_measureSegment_posDef (I : chebyshev1.SpectralInterval) (m : ℕ)
    (ν η : ProbabilityMeasure (Spectrum I)) (hG : (momentGram I m ν).PosDef)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hs1 : s < 1) :
    (momentGram I m (measureSegment ν η s)).PosDef := by
  rw [measureSegment, dite_eq_left hs, momentGram_mixture,
    Real.coe_toNNReal _ (by linarith [hs.2]), Real.coe_toNNReal _ hs.1]
  exact (hG.smul (by linarith)).add_posSemidef
    ((momentGram_posSemidef I m η).smul hs.1)

end
end krylov.Design
