import krylov.Design.Certificate
import krylov.Reference.Christoffel
import krylov.OneGradient.AtomicProbability

/-!
Article: main_krylov, thm:B and lem:chebyshev-design, finite spectral dictionary.
Use: identify the all-measures design criterion with the already proved actual
finite Christoffel kernel, retaining the same nodes, weights and minimizer.
Source: the finite spectral L2 construction reused from jacobi.Finite.
-/

namespace krylov.Design
noncomputable section
open Set MeasureTheory Polynomial jacobi.Finite
open scoped ENNReal InnerProductSpace
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- Realize the proved finite probability weights at genuine points of a compact spectral space.
Article: main_krylov, thm:B. -/
def atomicProbability {N : ℕ} (M : DiscreteMeasure N) (z : Fin N → X) : ProbabilityMeasure X :=
  ⟨∑ i, ENNReal.ofReal (M.weight i) • Measure.dirac (z i), ⟨by
    simp only [Measure.finsetSum_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (M.positive i).le), M.probability,
      ENNReal.ofReal_one]⟩⟩

variable [BorelSpace X] [T2Space X]

/-- Polynomial-square integration against the genuine atomic design is the original spectral sum.
Article: main_krylov, thm:B.
Proof: split the true finite measure integral and evaluate every original weighted Dirac mass. -/
theorem polynomialEnergy_atomic {N : ℕ} (M : DiscreteMeasure N) (z : Fin N → X)
    (x : C(X, ℝ)) (hz : ∀ i, x (z i) = M.node i) (p : ℝ[X]) :
    polynomialEnergy x (atomicProbability M z) p = ‖M.evaluate p‖ ^ 2 := by
  unfold polynomialEnergy
  change (∫ t, (p.eval (x t)) ^ 2 ∂∑ i, ENNReal.ofReal (M.weight i) • Measure.dirac (z i)) = _
  rw [integral_finsetSum_measure (fun i _ =>
    (integrable_dirac (by finiteness)).smul_measure (by simp))]
  rw [← real_inner_self_eq_norm_sq, M.inner_evaluate]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (M.positive i).le, hz i]
  simp only [smul_eq_mul, pow_two, mul_assoc]

/-- The all-probability-measures criterion equals the original finite reciprocal kernel.
Article: main_krylov, thm:B, bridge to lem:chris.
Proof: the existing unique finite minimizer supplies both bounds on the actual variational infimum. -/
theorem christoffel_atomic {N m : ℕ} (M : DiscreteMeasure N) (hm : m < N)
    (z : Fin N → X) (x : C(X, ℝ)) (hz : ∀ i, x (z i) = M.node i) (a : ℝ) :
    christoffel m a x (atomicProbability M z) = (Reference.christoffelKernel M m a)⁻¹ := by
  apply le_antisymm
  · let p : Competitor m a :=
      ⟨Reference.christoffelPolynomial M m a, Reference.christoffelPolynomial_admissible M m a⟩
    have h := christoffel_le m a x (atomicProbability M z) p
    rw [polynomialEnergy_atomic M z x hz] at h
    exact h.trans_eq (Reference.christoffelPolynomial_norm M hm a)
  · apply le_ciInf
    intro p
    rw [polynomialEnergy_atomic M z x hz]
    exact (Reference.christoffel_minimum_unique M hm a p.property.1 p.property.2).1

/-- Below the number of active atoms the actual design information is strictly positive.
Article: main_krylov, thm:B, positive sensitivity denominators for finite spectra.
Proof: transfer the proved strict positivity of the original Christoffel kernel. -/
theorem christoffel_atomic_pos {N m : ℕ} (M : DiscreteMeasure N) (hm : m < N)
    (z : Fin N → X) (x : C(X, ℝ)) (hz : ∀ i, x (z i) = M.node i) (a : ℝ) :
    0 < christoffel m a x (atomicProbability M z) := by
  rw [christoffel_atomic M hm z x hz a]
  exact inv_pos.mpr (Reference.christoffelKernel_pos M m a)

end
end krylov.Design
