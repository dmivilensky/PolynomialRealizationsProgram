import «2610.05164v2».Continuum.MeasureOperator

/-!
Article: 2610.05164v2, Lemma 4.
Trace of the genuine finite-measure feature operator in every Hilbert basis.
Use: `«2610.05164v2».Continuum.measureOperator_trace` feeds
`«2610.05164v2».Continuum.traceClassMeasureOperator_trace` (trace Class Measure Operator trace).
-/
namespace «2610.05164v2».Continuum
noncomputable section
open MeasureTheory Real Set
open scoped InnerProductSpace BigOperators
set_option backward.isDefEq.respectTransparency false

/--
Trace of the genuine finite-measure feature operator in every Hilbert basis.

The value of a convergent infinite sum: `HasSum (fun i => inner ℝ (b i) (measureOperator σ (b
i))) (σ.real univ)`.

Use: `«2610.05164v2».Continuum.measureOperator_trace` uses this infinite-sum formula to
establish exact identity `(∑' i, inner ℝ (b i) (measureOperator σ (b i))) = σ.real univ`.

Article: 2610.05164v2, Lemma 4 via `«2610.05164v2».Continuum.measureOperator_trace`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem measureOperator_hasSum_trace {ι : Type*} (b : HilbertBasis ι ℝ FeatureSpace)
    (σ : Measure ℝ) [IsFiniteMeasure σ] :
    HasSum (fun i => inner ℝ (b i) (measureOperator σ (b i))) (σ.real univ) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  let : Countable ι := orthonormal_countable b.orthonormal
  have hi := hasSum_integral_of_dominated_convergence
    (F := fun i x => inner ℝ (feature x) (b i)^2) (f := fun _ => (1 : ℝ)) (μ := σ)
    (fun i x => inner ℝ (feature x) (b i)^2)
    (fun i => ((feature_continuous.inner continuous_const).pow 2).aestronglyMeasurable)
    (fun i => Filter.Eventually.of_forall (fun x => by
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (sq_nonneg (inner ℝ (feature x) (b i)))]
      ))
    (Filter.Eventually.of_forall (fun x => (feature_parseval b x).summable))
    (by
      have he : (fun x => ∑' i, inner ℝ (feature x) (b i)^2) = (fun _ => (1 : ℝ)) :=
        funext (fun x => (feature_parseval b x).tsum_eq)
      rw [he]
      exact integrable_const 1)
    (Filter.Eventually.of_forall (fun x => feature_parseval b x))
  have he (i : ι) : inner ℝ (b i) (measureOperator σ (b i)) =
      ∫ x, inner ℝ (feature x) (b i)^2 ∂σ := by
    rw [measureOperator_inner]
    simp only [pow_two]
  simp only [integral_const,smul_eq_mul,mul_one] at hi
  convert hi using 1
  funext i
  exact he i

/--
Exact identity `(∑' i, inner ℝ (b i) (measureOperator σ (b i))) = σ.real univ`.

Use: `«2610.05164v2».Continuum.traceClassMeasureOperator_trace` uses this identity to establish
exact identity `TraceClassOperator.trace b (traceClassMeasureOperator μ) = μ.real univ`.

Article: 2610.05164v2, Lemma 4.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.measureOperator_hasSum_trace`
with the arguments shown in the proof.
-/
theorem measureOperator_trace {ι : Type*} (b : HilbertBasis ι ℝ FeatureSpace)
    (σ : Measure ℝ) [IsFiniteMeasure σ] :
    (∑' i, inner ℝ (b i) (measureOperator σ (b i))) = σ.real univ :=
  (measureOperator_hasSum_trace b σ).tsum_eq

end
end «2610.05164v2».Continuum
