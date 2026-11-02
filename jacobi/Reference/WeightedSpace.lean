import jacobi.Reference.Orthogonality
import chebyshev2.Continuum.WeightedL2
import chebyshev2.SineContinuum.LegendreHilbertBasis

/-!
Article: jacobi, Theorem 2.1.
The original sine-power multiplier gives a genuine onto L2 isometry
from its weighted measure to Lebesgue measure. This reuses the complete
weighted-L2 equivalence of chebyshev2, including null endpoint zeros.
The weighted measure is finite, so the community continuous-function
density theorem applies to the actual reference polynomial system.
Use: shares the original Lebesgue Hilbert space and its measure instances across the two reference constructions.
-/
namespace jacobi.Reference
noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology ENNReal
attribute [local instance] Measure.Subtype.measureSpace

/-- The same concrete closed unit interval used by the earlier article's complete L2 basis.
Use: shares the original Lebesgue Hilbert space and its measure instances across the two reference constructions.
Article: jacobi, Theorem 2.1.
-/
abbrev Interval := chebyshev2.SineContinuum.LegendreInterval

/-- The actual real Lebesgue reference Hilbert space.
Use: contains both the original reference basis and the later transformed orthonormal basis of Proposition C.2.
Article: jacobi, Theorem C.5.
-/
abbrev Space := chebyshev2.SineContinuum.LegendreSpace

/-- Subtype Lebesgue measure on the actual reference interval has no atoms.
Use: removes the two null endpoints when applying the earlier weighted-L2 unitary.
Article: jacobi, Theorem C.5.
Proof: the subtype measure is the pullback of Lebesgue measure under its measurable embedding; every singleton maps to a real singleton. -/
instance interval_nullSingleton : NullSingletonClass (volume : Measure Interval) := by
  constructor
  intro t
  change (volume : Measure ℝ).comap ((↑) : Interval → ℝ) {t}=0
  rw [Measure.comap_apply ((↑) : Interval → ℝ) Subtype.val_injective
    (MeasurableEmbedding.subtype_coe measurableSet_Icc).measurableSet_image' volume (measurableSet_singleton t)]
  simp

/-- The physical open interval has full measure inside the actual closed reference subtype.
Use: the genuine sine-power multiplier is nonzero almost everywhere even though it vanishes at both endpoints.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: both endpoint singletons have zero subtype Lebesgue measure. -/
theorem interval_interior_ae : ∀ᵐ t : Interval ∂volume,(t:ℝ)∈Ioo 0 1 := by
  filter_upwards [(volume : Measure Interval).ae_ne (⟨0,by norm_num⟩ : Interval),
    (volume : Measure Interval).ae_ne (⟨1,by norm_num⟩ : Interval)] with t h0 h1
  exact ⟨lt_of_le_of_ne t.property.1 (fun h => h0 (Subtype.ext h.symm)),
    lt_of_le_of_ne t.property.2 (fun h => h1 (Subtype.ext h))⟩

/-- The actual reference sine-power multiplier as the earlier article's general weighted-L2 datum.
Use: obtains a genuine surjective multiplication unitary without repeating weighted measure or reciprocal-map proofs.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
-/
def hilbertWeight (a : ℝ) (ha : -1<a) : chebyshev2.Continuum.L2Weight (volume : Measure Interval) where
  w t := weight a t
  measurable := ((weight_properties ha).1.comp continuous_subtype_val).measurable
  nonzero := interval_interior_ae.mono (fun _ ht => (weight_pos a ht).ne')

/-- The actual reference weight measure is finite over the full original order range.
Use: continuous functions are genuinely dense in its L2 space and every continuous polynomial has an L2 class.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: the actual multiplier squared is continuous on the compact subtype, hence integrable. Its nonnegative integral defines a finite density measure. -/
instance hilbertWeight_finite (a : ℝ) (ha : -1<a) : IsFiniteMeasure (hilbertWeight a ha).measure := by
  -- This is the genuine density measure of the actual sine-power prefactor, not a measure specified by desired polynomial orthogonality.
  have hcont : Continuous (fun t : Interval => (weight a t)^2) :=
    ((weight_properties ha).1.comp continuous_subtype_val).pow 2
  have hi : Integrable (fun t : Interval => (weight a t)^2) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply isFiniteMeasure_withDensity
  exact (lintegral_ofReal_ne_top_iff_integrable hcont.aestronglyMeasurable
    (Eventually.of_forall fun t => sq_nonneg (weight a t))).mpr hi

/-- The actual onto reference multiplication unitary, reusing the general theorem of the earlier article.
Use: transports the dense complete weighted polynomial system to the genuine original reference waves.
Article: jacobi, Lemma C.1.
-/
def weightUnitary (a : ℝ) (ha : -1<a) :
    Lp ℝ 2 (hilbertWeight a ha).measure ≃ₗᵢ[ℝ] Space := (hilbertWeight a ha).equiv

end
end jacobi.Reference
