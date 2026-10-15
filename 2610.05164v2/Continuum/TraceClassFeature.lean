import «2610.05164v2».Continuum.TraceClassTrace
import «2610.05164v2».Continuum.ProjectorNorm
import «2610.05164v2».Continuum.MeasureTrace
import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure

/-!
Article: 2610.05164v2, Proposition 3.
Identification with mathlib's genuine signed/vector-measure integral, not just an independently
defined difference of two operators.
Use: `«2610.05164v2».Continuum.traceClassDensityOperator_val` feeds
`«2610.05164v2».Continuum.traceClassDensityOperator_trace` (trace Class Density Operator trace).
Proof chain: `«2610.05164v2».Comparison.Profile.signed_determinant_comparison` — 2610.05164v2,
Theorem 3.4; Signed determinant and square-trace comparisons.
Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for trace-class
operators. The needed form is proved here.
-/
namespace «2610.05164v2».Continuum
noncomputable section
open MeasureTheory Real Set
open scoped InnerProductSpace BigOperators
set_option backward.isDefEq.respectTransparency false

/--
Defines `traceClassFeature` of type `TraceClassOperator FeatureSpace` by `⟨featureProjection x,
(featureProjection_traceBound x).isTraceClass⟩`.

Use: `«2610.05164v2».Continuum.traceClassDensityOperator` uses this definition in the displayed
construction of `traceClassDensityOperator`. Its inputs and component formulas are fixed by
that definition.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.
-/
def traceClassFeature (x : ℝ) : TraceClassOperator FeatureSpace :=
  ⟨featureProjection x, (featureProjection_traceBound x).isTraceClass⟩

/--
Exact identity `(traceClassFeature x).val = featureProjection x`.

Use: `«2610.05164v2».Continuum.traceClassFeature_norm_sub` rewrites with this identity to
establish exact identity `‖traceClassFeature x-traceClassFeature y‖ = 2*sqrt (1-exp
(-2*|x-y|))`.

Article: 2610.05164v2, Proposition 3.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
@[simp] theorem traceClassFeature_val (x : ℝ) : (traceClassFeature x).val = featureProjection x := rfl

/--
Exact identity `‖traceClassFeature x‖ = 1`.

Use: `«2610.05164v2».Continuum.traceClassDensity_integrable` rewrites with this identity to
establish integrability of the displayed function: `Integrable (fun x => m x •
traceClassFeature x)`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.TraceClassOperator.norm_def`,
`«2610.05164v2».Continuum.nuclearNorm_rankOne`, `«2610.05164v2».Continuum.feature_norm` with
the arguments shown in the proof.
-/
theorem traceClassFeature_norm (x : ℝ) : ‖traceClassFeature x‖ = 1 := by
  rw [TraceClassOperator.norm_def]
  change (nuclearNorm (InnerProductSpace.rankOne ℝ (feature x) (feature x))).toReal = 1
  rw [nuclearNorm_rankOne, feature_norm, mul_one]
  norm_num

/--
Exact identity `‖traceClassFeature x-traceClassFeature y‖ = 2*sqrt (1-exp (-2*|x-y|))`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Proposition 3.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.TraceClassOperator.norm_def`,
`«2610.05164v2».Continuum.TraceClassOperator.val_sub`,
`«2610.05164v2».Continuum.traceClassFeature_val` with the arguments shown in the proof.
-/
theorem traceClassFeature_norm_sub (x y : ℝ) :
    ‖traceClassFeature x-traceClassFeature y‖ = 2*sqrt (1-exp (-2*|x-y|)) := by
  rw [TraceClassOperator.norm_def, TraceClassOperator.val_sub,
    traceClassFeature_val, traceClassFeature_val, featureProjection_nuclearNorm_sub,
    ENNReal.toReal_ofReal (by positivity)]

/--
Continuity of the displayed function: `Continuous traceClassFeature`.

Use: `«2610.05164v2».Continuum.traceClassDensity_integrable` uses this continuity result to
establish integrability of the displayed function: `Integrable (fun x => m x •
traceClassFeature x)`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.feature_continuous`,
`«2610.05164v2».Continuum.nuclearNorm_toReal_le`,
`«2610.05164v2».Continuum.featureProjection_difference_traceBound` with the arguments shown in
the proof.
-/
theorem traceClassFeature_continuous : Continuous traceClassFeature := by
  -- Use the identities/estimates `«2610.05164v2».Continuum.feature_continuous`,
  -- `«2610.05164v2».Continuum.nuclearNorm_toReal_le`,
  -- `«2610.05164v2».Continuum.featureProjection_difference_traceBound` with the arguments
  -- shown in the proof.
  apply Metric.continuous_iff.mpr
  intro y ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.continuous_iff.mp feature_continuous y (ε/2) (by positivity)
  refine ⟨δ, hδ, fun x hx => ?_⟩
  have hb := nuclearNorm_toReal_le (featureProjection_difference_traceBound x y)
  change (nuclearNorm (featureProjection x-featureProjection y)).toReal ≤ _ at hb
  rw [dist_eq_norm]
  change (nuclearNorm (featureProjection x-featureProjection y)).toReal < ε
  have he : ‖feature x-feature y‖ < ε/2 := by simpa only [dist_eq_norm] using hd x hx
  linarith

/--
Integrability of the displayed function: `Integrable traceClassFeature μ`.

Use: `«2610.05164v2».Continuum.traceClassMeasureOperator_val` uses this integrability result to
establish exact identity `(traceClassMeasureOperator μ).val = measureOperator μ`.

Article: 2610.05164v2, Proposition 3.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.traceClassFeature_continuous`,
`«2610.05164v2».Continuum.traceClassFeature_norm` with the arguments shown in the proof.
-/
theorem traceClassFeature_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable traceClassFeature μ := by
  apply (integrable_const (μ := μ) (1 : ℝ)).mono'
    traceClassFeature_continuous.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => (traceClassFeature_norm x).le)

/--
Positive-measure feature integral taken in the nuclear-norm Banach space.

Use: `«2610.05164v2».Continuum.traceClassMeasureOperator_norm` uses this definition to
establish the stated quantitative bound `‖traceClassMeasureOperator μ‖ ≤ μ.real univ`.

Article: 2610.05164v2, Proposition 3.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.
-/
def traceClassMeasureOperator (μ : Measure ℝ) : TraceClassOperator FeatureSpace :=
  ∫ x, traceClassFeature x ∂μ

/--
Exact identity `(traceClassMeasureOperator μ).val = measureOperator μ`.

Use: `«2610.05164v2».Continuum.traceClassMeasureOperator_trace` rewrites with this identity to
establish exact identity `TraceClassOperator.trace b (traceClassMeasureOperator μ) = μ.real
univ`.

Article: 2610.05164v2, Proposition 3.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.traceClassFeature_integrable`
with the arguments shown in the proof.
-/
theorem traceClassMeasureOperator_val (μ : Measure ℝ) [IsFiniteMeasure μ] :
    (traceClassMeasureOperator μ).val = measureOperator μ :=
  ((TraceClassOperator.toOperator FeatureSpace).integral_comp_comm
    (traceClassFeature_integrable μ)).symm
/--
The stated quantitative bound `‖traceClassMeasureOperator μ‖ ≤ μ.real univ`.

Use: `«2610.05164v2».Continuum.traceClassSignedOperator_norm` uses this bound to establish the
stated quantitative bound `‖traceClassSignedOperator σ‖ ≤ σ.totalVariation.real univ`.

Article: 2610.05164v2, Proposition 3.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.traceClassFeature_norm` with the
arguments shown in the proof.
-/
theorem traceClassMeasureOperator_norm (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ‖traceClassMeasureOperator μ‖ ≤ μ.real univ := by
  have h := norm_integral_le_integral_norm (f := traceClassFeature) (μ := μ)
  simpa only [traceClassMeasureOperator, traceClassFeature_norm, integral_const,
    smul_eq_mul, mul_one] using h

/--
Exact identity `TraceClassOperator.trace b (traceClassMeasureOperator μ) = μ.real univ`.

Use: `«2610.05164v2».Continuum.traceClassSignedOperator_trace` rewrites with this identity to
establish exact identity `TraceClassOperator.trace b (traceClassSignedOperator σ) = σ univ`.

Article: 2610.05164v2, Proposition 3.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.TraceClassOperator.trace_apply`,
`«2610.05164v2».Continuum.traceClassMeasureOperator_val`,
`«2610.05164v2».Continuum.measureOperator_trace` with the arguments shown in the proof.
-/
theorem traceClassMeasureOperator_trace {ι : Type*} (b : HilbertBasis ι ℝ FeatureSpace)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    TraceClassOperator.trace b (traceClassMeasureOperator μ) = μ.real univ := by
  rw [TraceClassOperator.trace_apply, traceClassMeasureOperator_val]
  exact measureOperator_trace b μ

/--
The Hahn--Jordan Bochner integral of the feature family in trace class. Both component
integrals exist for every finite signed Borel measure.

Use: `«2610.05164v2».Continuum.traceClassSignedOperator_trace` rewrites with this definition to
establish exact identity `TraceClassOperator.trace b (traceClassSignedOperator σ) = σ univ`.

Article: 2610.05164v2, Proposition 3.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.
-/
def traceClassSignedOperator (σ : SignedMeasure ℝ) : TraceClassOperator FeatureSpace :=
  traceClassMeasureOperator σ.toJordanDecomposition.posPart -
    traceClassMeasureOperator σ.toJordanDecomposition.negPart

/--
The stated quantitative bound `‖traceClassSignedOperator σ‖ ≤ σ.totalVariation.real univ`.

Use: `«2610.05164v2».Sobolev.sobolevSignedOperator_spec` uses this bound to establish exact
identity `sobolevSignedOperator σ=(∫ᵛ x, traceClassFeature x ∂<•σ) ∧ ‖sobolevSignedOperator σ‖
≤ σ.totalVariation.real univ ∧ TraceClassOperator.trace b (sobolevSignedOperator σ)=σ univ`.

Article: 2610.05164v2, Proposition 3.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.traceClassMeasureOperator_norm`
with the arguments shown in the proof.
-/
theorem traceClassSignedOperator_norm (σ : SignedMeasure ℝ) :
    ‖traceClassSignedOperator σ‖ ≤ σ.totalVariation.real univ := by
  apply (norm_sub_le _ _).trans
  rw [SignedMeasure.totalVariation, measureReal_add_apply]
  exact add_le_add (traceClassMeasureOperator_norm _) (traceClassMeasureOperator_norm _)

/--
Exact identity `TraceClassOperator.trace b (traceClassSignedOperator σ) = σ univ`.

Use: `«2610.05164v2».Sobolev.sobolevSignedOperator_spec` uses this identity to establish exact
identity `sobolevSignedOperator σ=(∫ᵛ x, traceClassFeature x ∂<•σ) ∧ ‖sobolevSignedOperator σ‖
≤ σ.totalVariation.real univ ∧ TraceClassOperator.trace b (sobolevSignedOperator σ)=σ univ`.

Article: 2610.05164v2, Proposition 3.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.traceClassMeasureOperator_trace`
with the arguments shown in the proof.
-/
theorem traceClassSignedOperator_trace {ι : Type*} (b : HilbertBasis ι ℝ FeatureSpace)
    (σ : SignedMeasure ℝ) : TraceClassOperator.trace b (traceClassSignedOperator σ) = σ univ := by
  rw [traceClassSignedOperator, map_sub, traceClassMeasureOperator_trace,
    traceClassMeasureOperator_trace]
  exact (σ.apply_eq_posPart_real_sub_negPart_real MeasurableSet.univ).symm

/--
The precise assertion is `σ.Integrable traceClassFeature`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Proposition 3.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.traceClassFeature_integrable`
with the arguments shown in the proof.
-/
theorem traceClassSignedOperator_integrable (σ : SignedMeasure ℝ) :
    σ.Integrable traceClassFeature := by
  change Integrable traceClassFeature σ.variation
  rw [← SignedMeasure.totalVariation_eq_variation]
  exact traceClassFeature_integrable _

/--
Identification with mathlib's genuine signed/vector-measure integral, not just an independently
defined difference of two operators.

Exact identity `traceClassSignedOperator σ = ∫ᵛ x, traceClassFeature x ∂<•σ`.

Use: `«2610.05164v2».Continuum.traceClassSignedOperator_positive_measure` rewrites with this
identity to establish the identity `(traceClassSignedOperator μ.toSignedMeasure).val =
measureOperator μ`.

Article: 2610.05164v2, Proposition 3.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.traceClassFeature_integrable`
with the arguments shown in the proof.
-/
theorem traceClassSignedOperator_eq_integral (σ : SignedMeasure ℝ) :
    traceClassSignedOperator σ = ∫ᵛ x, traceClassFeature x ∂<•σ := by
  -- Use the identities/estimates `«2610.05164v2».Continuum.traceClassFeature_integrable` with
  -- the arguments shown in the proof.
  have hp : σ.toJordanDecomposition.posPart.toSignedMeasure.Integrable traceClassFeature := by
    change Integrable traceClassFeature σ.toJordanDecomposition.posPart.toSignedMeasure.variation
    rw [Measure.variation_toSignedMeasure]
    exact traceClassFeature_integrable _
  have hn : σ.toJordanDecomposition.negPart.toSignedMeasure.Integrable traceClassFeature := by
    change Integrable traceClassFeature σ.toJordanDecomposition.negPart.toSignedMeasure.variation
    rw [Measure.variation_toSignedMeasure]
    exact traceClassFeature_integrable _
  symm
  conv_lhs => rw [← σ.toSignedMeasure_toJordanDecomposition, JordanDecomposition.toSignedMeasure]
  rw [VectorMeasure.integral_sub_vectorMeasure hp hn, VectorMeasure.integral_toSignedMeasure,
    VectorMeasure.integral_toSignedMeasure]
  rfl

/--
Exact identity `(traceClassSignedOperator μ.toSignedMeasure).val = measureOperator μ`.

Use: `«2610.05164v2».Continuum.traceClassSignedOperator_positive` rewrites with this identity
to establish `(traceClassSignedOperator
μ.toSignedMeasure).val.IsPositive`.

Article: 2610.05164v2, Proposition 3.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: Use the identities/estimates
`«2610.05164v2».Continuum.traceClassSignedOperator_eq_integral`,
`«2610.05164v2».Continuum.traceClassMeasureOperator_val` with the arguments shown in the proof.
-/
theorem traceClassSignedOperator_positive_measure (μ : Measure ℝ) [IsFiniteMeasure μ] :
    (traceClassSignedOperator μ.toSignedMeasure).val = measureOperator μ := by
  rw [traceClassSignedOperator_eq_integral, VectorMeasure.integral_toSignedMeasure]
  exact traceClassMeasureOperator_val μ

/--
The precise assertion is `(traceClassSignedOperator μ.toSignedMeasure).val.IsPositive`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Proposition 3.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: Use the identities/estimates
`«2610.05164v2».Continuum.traceClassSignedOperator_positive_measure`,
`«2610.05164v2».Continuum.measureOperator_positive` with the arguments shown in the proof.
-/
theorem traceClassSignedOperator_positive (μ : Measure ℝ) [IsFiniteMeasure μ] :
    (traceClassSignedOperator μ.toSignedMeasure).val.IsPositive := by
  rw [traceClassSignedOperator_positive_measure]
  exact measureOperator_positive μ

/--
Integrability of the displayed function: `Integrable (fun x => m x • traceClassFeature x)`.

Use: `«2610.05164v2».Continuum.traceClassDensityOperator_val` uses this integrability result to
establish exact identity `(traceClassDensityOperator m).val = densityOperator m`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.traceClassFeature_continuous`,
`«2610.05164v2».Continuum.traceClassFeature_norm` with the arguments shown in the proof.
-/
theorem traceClassDensity_integrable {m : ℝ → ℝ} (hm : Integrable m) :
    Integrable (fun x => m x • traceClassFeature x) := by
  apply hm.norm.mono'
  · exact hm.aestronglyMeasurable.smul traceClassFeature_continuous.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun x => by rw [norm_smul, traceClassFeature_norm, mul_one])

/--
Defines `traceClassDensityOperator` of type `TraceClassOperator FeatureSpace` by `∫ x, m x •
traceClassFeature x`.

Use: `«2610.05164v2».Continuum.traceClassDensityOperator_trace` uses this definition to
establish exact identity `TraceClassOperator.trace b (traceClassDensityOperator m) = ∫ x, m x`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.
-/
def traceClassDensityOperator (m : ℝ → ℝ) : TraceClassOperator FeatureSpace :=
  ∫ x, m x • traceClassFeature x

/--
Exact identity `(traceClassDensityOperator m).val = densityOperator m`.

Use: `«2610.05164v2».Continuum.traceClassDensityOperator_trace` rewrites with this identity to
establish exact identity `TraceClassOperator.trace b (traceClassDensityOperator m) = ∫ x, m x`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.traceClassDensity_integrable`
with the arguments shown in the proof.
-/
theorem traceClassDensityOperator_val {m : ℝ → ℝ} (hm : Integrable m) :
    (traceClassDensityOperator m).val = densityOperator m :=
  ((TraceClassOperator.toOperator FeatureSpace).integral_comp_comm
    (traceClassDensity_integrable hm)).symm
/--
Exact identity `TraceClassOperator.trace b (traceClassDensityOperator m) = ∫ x, m x`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Proposition 3.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.TraceClassOperator.trace_apply`,
`«2610.05164v2».Continuum.traceClassDensityOperator_val`,
`«2610.05164v2».Continuum.densityOperator_trace` with the arguments shown in the proof.
-/
theorem traceClassDensityOperator_trace {ι : Type*} (b : HilbertBasis ι ℝ FeatureSpace)
    {m : ℝ → ℝ} (hm : Integrable m) :
    TraceClassOperator.trace b (traceClassDensityOperator m) = ∫ x, m x := by
  rw [TraceClassOperator.trace_apply, traceClassDensityOperator_val hm]
  exact densityOperator_trace b hm

end
end «2610.05164v2».Continuum
