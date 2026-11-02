import krylov.OneGradient.PolynomialMoments
import Mathlib.MeasureTheory.Measure.Dirac.Basic
set_option autoImplicit false
/-!
Article: main_krylov, s5:moment(b), actual finite spectral probability measures.
Use: realize every constructed physical spectral completion as a genuine
MeasureTheory probability measure in the original all-measures moment problem.
Source: finite positive weighted Dirac measures and the standard actual Bochner
integral over a finite measure sum; no probability or integrability is assumed.
-/

namespace krylov.OneGradient
noncomputable section
open Polynomial MeasureTheory jacobi.Finite
open scoped BigOperators ENNReal

/-- The original finite positive spectral data as an actual probability measure.
Use: supply genuine measures, rather than finite-sum surrogates, for the reverse
attainment direction of the original arbitrary-measure moment interval.
Article: main_krylov, s5:moment(b). -/
def discreteAtomicMeasure {N : ℕ} (M : DiscreteMeasure N) : Measure ℝ :=
  ∑ i,ENNReal.ofReal (M.weight i) • Measure.dirac (M.node i)

/-- The actual finite spectral measure has total mass exactly one.
Use: every physical completion is a genuine candidate in the all-probability-measure problem.
Article: main_krylov, s5:moment(b).
Proof: each true Dirac mass has mass one, and positivity transports the
original real probability normalization through ENNReal.ofReal. -/
instance discreteAtomicMeasure_probability {N : ℕ} (M : DiscreteMeasure N) :
    IsProbabilityMeasure (discreteAtomicMeasure M) where
  measure_univ := by
    simp only [discreteAtomicMeasure,Measure.finsetSum_apply,Measure.smul_apply,
      measure_univ,smul_eq_mul,mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (M.positive i).le),M.probability,ENNReal.ofReal_one]

/-- Every real function is integrable on the actual finite spectral probability measure.
Use: all real polynomial moments are genuine Bochner integrals, including
the first missing moment and the Radau endpoint rules.
Article: main_krylov, s5:moment(b).
Proof: any real function is integrable at each true finite Dirac mass; its
actual positive finite weight and the finite measure sum preserve integrability. -/
theorem discrete_atomic_integrable {N : ℕ} (M : DiscreteMeasure N) (f : ℝ → ℝ) :
    Integrable f (discreteAtomicMeasure M) := by
  apply integrable_finsetSum_measure.mpr
  intro i _
  exact (integrable_dirac (by finiteness)).smul_measure (by simp)

/-- Integration against the actual spectral probability measure is exactly
the original positive weighted spectral sum.
Use: transport every proved physical spectral moment to the genuine measure class.
Article: main_krylov, s5:moment(b).
Proof: actual finite integrability permits Bochner integration over the true
finite measure sum; each weighted Dirac integral is its real original weight. -/
theorem discrete_atomic_integral {N : ℕ} (M : DiscreteMeasure N) (f : ℝ → ℝ) :
    (∫ x,f x ∂discreteAtomicMeasure M)=∑ i,M.weight i*f (M.node i) := by
  rw [discreteAtomicMeasure,integral_finsetSum_measure (fun i _ =>
    (integrable_dirac (by finiteness)).smul_measure (by simp))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_smul_measure,integral_dirac,ENNReal.toReal_ofReal (M.positive i).le]
  rfl

/-- The true spectral nodes in a physical interval give almost everywhere
support of the actual probability measure in that same closed interval.
Use: constructed physical endpoint measures satisfy the original support condition.
Article: main_krylov, s5:moment(b).
Proof: each actual Dirac mass is supported at its own known spectral node;
the genuine finite measure sum preserves that almost everywhere property. -/
theorem discrete_atomic_supported {N : ℕ} (M : DiscreteMeasure N) (mu upper : ℝ)
    (hnodes : ∀ i,M.node i∈Set.Icc mu upper) :
    ∀ᵐ x ∂discreteAtomicMeasure M,x∈Set.Icc mu upper := by
  apply ae_finsetSum_measure_iff.mpr
  intro i _
  exact Measure.ae_smul_measure ((ae_dirac_iff measurableSet_Icc).mpr (hnodes i)) _

/-- The actual finite spectral probability integral has exactly the original
polynomial-functional representation.
Use: connect actual measures to the finite-polynomial proof without changing moments.
Article: main_krylov, s5:moment(b).
Proof: specialize the actual spectral integral identity to genuine polynomial evaluation. -/
theorem discrete_atomic_polynomial_integral {N : ℕ} (M : DiscreteMeasure N) (p : ℝ[X]) :
    (∫ x,p.eval x ∂discreteAtomicMeasure M)=discretePolynomialIntegral M p :=
  discrete_atomic_integral M (fun x => p.eval x)

end
end krylov.OneGradient
