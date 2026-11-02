import krylov.Design.MixedObjective
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Tactic

/-!
Article: main_krylov, thm:B, concavity on the full probability-measure domain.
Use: compare actual mixtures before any invertibility or support-size assumption.
Source: Pukelsheim93, an infimum of linear energy criteria is concave.
-/

namespace krylov.Design
noncomputable section
open Set MeasureTheory Polynomial
open scoped NNReal ENNReal
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- The genuine convex combination of probability measures, with nonnegative weights.
Article: main_krylov, thm:B. -/
def mixture (ν η : ProbabilityMeasure X) (a b : ℝ≥0) (hab : a + b = 1) :
    ProbabilityMeasure X :=
  ⟨a • (ν : Measure X) + b • (η : Measure X), ⟨by
    simp only [Measure.add_apply, Measure.smul_apply, measure_univ]
    change (a : ℝ≥0∞) * 1 + (b : ℝ≥0∞) * 1 = 1
    simp only [mul_one]
    exact_mod_cast hab⟩⟩

variable [CompactSpace X] [BorelSpace X]

/-- Polynomial energy is affine under actual probability mixtures.
Article: main_krylov, thm:B. Proof: compact polynomial integrability permits splitting the integral. -/
theorem polynomialEnergy_mixture (x : C(X, ℝ)) (ν η : ProbabilityMeasure X)
    (a b : ℝ≥0) (hab : a + b = 1) (p : ℝ[X]) :
    polynomialEnergy x (mixture ν η a b hab) p =
      (a : ℝ) * polynomialEnergy x ν p + (b : ℝ) * polynomialEnergy x η p := by
  have hi (μ : Measure X) [IsFiniteMeasure μ] : Integrable (fun t => (p.eval (x t)) ^ 2) μ := by
    exact ((p.continuous.comp x.continuous).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ t, (p.eval (x t)) ^ 2 ∂(a • (ν : Measure X) + b • (η : Measure X))) = _
  rw [integral_add_measure (hi _) (hi _), integral_smul_nnreal_measure,
    integral_smul_nnreal_measure]
  rfl

/-- Information is concave even at a singular endpoint of a measure segment.
Article: main_krylov, thm:B.
Proof: the energy of every competitor dominates the same mixture of both infima. -/
theorem christoffel_mixture_le (m : ℕ) (z : ℝ) (x : C(X, ℝ))
    (ν η : ProbabilityMeasure X) (a b : ℝ≥0) (hab : a + b = 1) :
    (a : ℝ) * christoffel m z x ν + (b : ℝ) * christoffel m z x η ≤
      christoffel m z x (mixture ν η a b hab) := by
  apply le_ciInf
  intro p
  rw [polynomialEnergy_mixture]
  exact add_le_add (mul_le_mul_of_nonneg_left (christoffel_le m z x ν p) a.coe_nonneg)
    (mul_le_mul_of_nonneg_left (christoffel_le m z x η p) b.coe_nonneg)

/-- The article's full range of exponents gives a concave mixed objective.
Article: main_krylov, thm:B, including gamma=1 and zero weights.
Proof: compose information concavity with the increasing concave real power. -/
theorem mixedObjective_mixture_le (M : ℕ) (w : Fin M → ℝ) (hw : ∀ i, 0 ≤ w i)
    {γ : ℝ} (hγ₀ : 0 ≤ γ) (hγ₁ : γ ≤ 1) (z : ℝ) (x : C(X, ℝ))
    (ν η : ProbabilityMeasure X) (a b : ℝ≥0) (hab : a + b = 1) :
    (a : ℝ) * mixedObjective M w γ z x ν + (b : ℝ) * mixedObjective M w γ z x η ≤
      mixedObjective M w γ z x (mixture ν η a b hab) := by
  unfold mixedObjective
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hab' : (a : ℝ) + (b : ℝ) = 1 := by exact_mod_cast hab
  have hp := (Real.concaveOn_rpow hγ₀ hγ₁).2
    (christoffel_nonneg (i.val + 1) z x ν)
    (christoffel_nonneg (i.val + 1) z x η) a.coe_nonneg b.coe_nonneg hab'
  have hc := christoffel_mixture_le (i.val + 1) z x ν η a b hab
  have hn : 0 ≤ (a : ℝ) * christoffel (i.val + 1) z x ν +
      (b : ℝ) * christoffel (i.val + 1) z x η :=
    add_nonneg (mul_nonneg a.coe_nonneg (christoffel_nonneg _ _ _ _))
      (mul_nonneg b.coe_nonneg (christoffel_nonneg _ _ _ _))
  have hb := hp.trans (Real.rpow_le_rpow hn hc hγ₀)
  simpa only [smul_eq_mul, mul_add, mul_left_comm] using mul_le_mul_of_nonneg_left hb (hw i)

end
end krylov.Design
