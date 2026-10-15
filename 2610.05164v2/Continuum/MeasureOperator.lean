import «2610.05164v2».Continuum.CompactEigenbasis

/-!
Article: 2610.05164v2, Lemma 4.
The first, integral form of the transport nuclear bound.
Use: `«2610.05164v2».Continuum.measureOperator_transport_integral` feeds
`«2610.05164v2».Continuum.measureOperator_transport` (Lemma 4(v), with the article's transport
constant).
Proof chain: `«2610.05164v2».Packing.packed_spectral_distance` — 2610.05164v2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
-/
namespace «2610.05164v2».Continuum
noncomputable section
open MeasureTheory Real Set
open scoped InnerProductSpace BigOperators
set_option backward.isDefEq.respectTransparency false

/--
Feature operator of an actual finite positive Borel measure.

Use: `«2610.05164v2».Continuum.measureOperator_inner` rewrites with this definition to
establish exact identity `inner ℝ u (measureOperator σ v) = ∫ x, inner ℝ (feature x) u * inner
ℝ (feature x) v ∂σ`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.
-/
def measureOperator (σ : Measure ℝ) : FeatureSpace →L[ℝ] FeatureSpace := ∫ x, featureProjection x ∂σ

/--
Integrability of the displayed function: `Integrable featureProjection σ`.

Use: `«2610.05164v2».Continuum.measureOperator_inner` rewrites with this integrability result
to establish the identity `inner ℝ u (measureOperator σ v) = ∫ x, inner ℝ (feature x) u *
inner ℝ (feature x) v ∂σ`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.featureProjection_continuous`,
`«2610.05164v2».Continuum.featureProjection_norm` with the arguments shown in the proof.
-/
theorem featureProjection_integrable (σ : Measure ℝ) [IsFiniteMeasure σ] :
    Integrable featureProjection σ := by
  apply (integrable_const (μ := σ) (1 : ℝ)).mono' featureProjection_continuous.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => (featureProjection_norm x).le)

/--
The precise assertion is `TraceBound (measureOperator σ) (σ.real univ)`.

Use: `«2610.05164v2».Continuum.measureOperator_isTraceClass` uses this assertion to establish
the trace-class property: `IsTraceClass (measureOperator σ)`.

Article: 2610.05164v2, Lemma 4.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.traceBound_integral`,
`«2610.05164v2».Continuum.featureProjection_integrable`,
`«2610.05164v2».Continuum.featureProjection_traceBound` with the arguments shown in the proof.
-/
theorem measureOperator_traceBound (σ : Measure ℝ) [IsFiniteMeasure σ] :
    TraceBound (measureOperator σ) (σ.real univ) := by
  have h := traceBound_integral (featureProjection_integrable σ)
    (integrable_const (μ := σ) (1 : ℝ))
    (Filter.Eventually.of_forall featureProjection_traceBound)
  simpa only [measureOperator, integral_const, smul_eq_mul, mul_one] using h

/--
The trace-class property: `IsTraceClass (measureOperator σ)`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 4.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.TraceBound.isTraceClass`,
`«2610.05164v2».Continuum.measureOperator_traceBound` with the arguments shown in the proof.
-/
theorem measureOperator_isTraceClass (σ : Measure ℝ) [IsFiniteMeasure σ] : IsTraceClass (measureOperator σ) :=
  (measureOperator_traceBound σ).isTraceClass

/--
Compactness of the displayed operator: `IsCompactOperator (measureOperator σ)`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 4.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.integral_mem_closedSubmodule`,
`«2610.05164v2».Continuum.featureProjection_integrable`,
`«2610.05164v2».Continuum.featureProjection_isCompact` with the arguments shown in the proof.
-/
theorem measureOperator_isCompact (σ : Measure ℝ) [IsFiniteMeasure σ] : IsCompactOperator (measureOperator σ) := by
  let S := compactOperator (RingHom.id ℝ) FeatureSpace FeatureSpace
  apply integral_mem_closedSubmodule S isClosed_setOfPred_isCompactOperator (featureProjection_integrable σ)
  exact Filter.Eventually.of_forall featureProjection_isCompact

/--
Exact identity `inner ℝ u (measureOperator σ v) = ∫ x, inner ℝ (feature x) u * inner ℝ (feature
x) v ∂σ`.

Use: `«2610.05164v2».Continuum.measureOperator_positive` rewrites with this identity to
establish the precise assertion is `(measureOperator σ).IsPositive`.

Article: 2610.05164v2, Lemma 4 via `«2610.05164v2».Continuum.measureOperator_trace`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem measureOperator_inner (σ : Measure ℝ) [IsFiniteMeasure σ] (u v : FeatureSpace) :
    inner ℝ u (measureOperator σ v) =
      ∫ x, inner ℝ (feature x) u * inner ℝ (feature x) v ∂σ := by
  rw [measureOperator, ContinuousLinearMap.integral_apply (featureProjection_integrable σ) v,
    ← integral_inner ((featureProjection_integrable σ).apply_continuousLinearMap v) u]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun x => featureProjection_inner x u v))

/--
The precise assertion is `(measureOperator σ).IsPositive`.

Use: `«2610.05164v2».Continuum.traceClassSignedOperator_positive` uses this assertion to
establish the precise assertion is `(traceClassSignedOperator
μ.toSignedMeasure).val.IsPositive`.

Article: 2610.05164v2, Lemma 4.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem measureOperator_positive (σ : Measure ℝ) [IsFiniteMeasure σ] : (measureOperator σ).IsPositive := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  constructor
  · intro u v
    change inner ℝ (measureOperator σ u) v = inner ℝ u (measureOperator σ v)
    rw [real_inner_comm, measureOperator_inner, measureOperator_inner]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun _ => mul_comm _ _))
  · intro u
    change 0 ≤ inner ℝ (measureOperator σ u) u
    rw [real_inner_comm, measureOperator_inner]
    exact integral_nonneg (fun _ => mul_self_nonneg _)

/--
Marginal identities for the genuine Bochner integrals.

Exact identity `measureOperator (μ.map Prod.fst) - measureOperator (μ.map Prod.snd) = ∫ z,
featureProjection z.1 - featureProjection z.2 ∂μ`.

Use: `«2610.05164v2».Continuum.measureOperator_transport_integral` rewrites with this identity
to establish `TraceBound (measureOperator (μ.map Prod.fst) -
measureOperator (μ.map Prod.snd)) (∫ z, 2 * ‖feature z.1 - feature z.2‖ ∂μ)`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.featureProjection_continuous`,
`«2610.05164v2».Continuum.featureProjection_integrable` with the arguments shown in the proof.
-/
theorem measureOperator_marginal_difference (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] :
    measureOperator (μ.map Prod.fst) - measureOperator (μ.map Prod.snd) =
      ∫ z, featureProjection z.1 - featureProjection z.2 ∂μ := by
  -- Use the identities/estimates `«2610.05164v2».Continuum.featureProjection_continuous`,
  -- `«2610.05164v2».Continuum.featureProjection_integrable` with the arguments shown in the
  -- proof.
  unfold measureOperator
  rw [integral_map measurable_fst.aemeasurable featureProjection_continuous.aestronglyMeasurable,
    integral_map measurable_snd.aemeasurable featureProjection_continuous.aestronglyMeasurable,
    integral_sub]
  · exact (featureProjection_integrable (μ.map Prod.fst)).comp_measurable measurable_fst
  · exact (featureProjection_integrable (μ.map Prod.snd)).comp_measurable measurable_snd

/--
The first, integral form of the transport nuclear bound.

The precise assertion is `TraceBound (measureOperator (μ.map Prod.fst) - measureOperator (μ.map
Prod.snd)) (∫ z, 2 * ‖feature z.1 - feature z.2‖ ∂μ)`.

Use: `«2610.05164v2».Continuum.measureOperator_transport` uses this assertion to establish the
precise assertion is `TraceBound (measureOperator (μ.map Prod.fst) - measureOperator (μ.map
Prod.snd)) (2 * sqrt (2 * μ.real univ * ∫ z, |z.1-z.2| ∂μ))`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Proof: Use the identities/estimates
`«2610.05164v2».Continuum.measureOperator_marginal_difference`,
`«2610.05164v2».Continuum.traceBound_integral`,
`«2610.05164v2».Continuum.featureProjection_integrable` with the arguments shown in the proof.
-/
theorem measureOperator_transport_integral (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] :
    TraceBound (measureOperator (μ.map Prod.fst) - measureOperator (μ.map Prod.snd))
      (∫ z, 2 * ‖feature z.1 - feature z.2‖ ∂μ) := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Continuum.measureOperator_marginal_difference`,
  -- `«2610.05164v2».Continuum.traceBound_integral`,
  -- `«2610.05164v2».Continuum.featureProjection_integrable` with the arguments shown in the
  -- proof.
  rw [measureOperator_marginal_difference]
  apply traceBound_integral
  · exact ((featureProjection_integrable (μ.map Prod.fst)).comp_measurable measurable_fst).sub
      ((featureProjection_integrable (μ.map Prod.snd)).comp_measurable measurable_snd)
  · apply (integrable_const (μ := μ) (4 : ℝ)).mono'
    · exact ((feature_continuous.comp continuous_fst).sub
        (feature_continuous.comp continuous_snd)).norm.aestronglyMeasurable.const_mul 2
    · exact Filter.Eventually.of_forall (fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have h := norm_sub_le (feature z.1) (feature z.2)
        rw [feature_norm, feature_norm] at h
        linarith)
  · exact Filter.Eventually.of_forall (fun z => featureProjection_difference_traceBound z.1 z.2)

end
end «2610.05164v2».Continuum
