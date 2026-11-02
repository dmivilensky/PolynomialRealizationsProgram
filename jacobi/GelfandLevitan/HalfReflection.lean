import jacobi.GelfandLevitan.HalfProjection
import chebyshev2.Continuum.MeasureUnitary
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
Article: jacobi, Proposition C.2.
Physical reflection is a genuine measure-preserving L2 unitary. It
interchanges the two physical half projections, while the actual full
reference basis has the printed alternating reflection signs.
Use: constructs the two complete half-interval reference bases by their even and odd extensions.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory Filter jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false

/-- The actual physical midpoint reflection on the original full L2 space.
Use: constructs the two complete half-interval reference bases by their even and odd extensions.
Article: jacobi, Proposition 2.2.
Source: the earlier article's measureUnitary and mathlib's measure-preserving unit-interval reflection. -/
def reflectionUnitary : Space ≃ₗᵢ[ℝ] Space :=
  chebyshev2.Continuum.measureUnitary unitInterval.symmMeasurableEquiv
    unitInterval.measurePreserving_symm

/-- Reflection has exactly its original spatial representative almost everywhere.
Use: the half-projection partition and the reference parity signs concern the actual original physical reflection.
Article: jacobi, Proposition C.2.
Proof: reuse the earlier measure-unitary representative theorem for the original measure-preserving reflection. -/
theorem reflectionUnitary_ae (v : Space) :
    reflectionUnitary v=ᵐ[volume] fun t:Interval => v (unitInterval.symm t) :=
  chebyshev2.Continuum.measureUnitary_ae _ _ v

/-- Applying the true physical reflection twice gives the original Hilbert vector.
Use: makes its genuine unitary symmetric and identifies the reflected half projection.
Article: jacobi, Proposition C.2.
Proof: compose the actual Lp pullbacks and use the pointwise involution of the original reflection. -/
theorem reflectionUnitary_involutive (v : Space) :
    reflectionUnitary (reflectionUnitary v)=v := by
  change Lp.compMeasurePreserving unitInterval.symm unitInterval.measurePreserving_symm
    (Lp.compMeasurePreserving unitInterval.symm unitInterval.measurePreserving_symm v)=v
  rw [← Lp.compMeasurePreserving_comp_apply]
  have he : unitInterval.symm ∘ unitInterval.symm=id := funext unitInterval.symm_symm
  simp only [he,Lp.compMeasurePreserving_id_apply]

/-- The actual physical reflection is symmetric for the original L2 inner product.
Use: transfers coefficients between a vector and its genuine parity extension in the half-basis completeness proof.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Proof: apply the true unitary inner-product identity to v and the reflection of w, then use its genuine involution. -/
theorem reflectionUnitary_inner (v w : Space) :
    inner ℝ (reflectionUnitary v) w=inner ℝ v (reflectionUnitary w) := by
  have h := reflectionUnitary.inner_map_map v (reflectionUnitary w)
  rwa [reflectionUnitary_involutive] at h

/-- The original reference basis has its exact alternating physical reflection sign.
Use: splits the complete full reference basis into its two complete half-interval classes.
Article: jacobi, Proposition C.2.
Proof: transport the actual normalized reference representative through the measure-preserving reflection and apply the proved original Gegenbauer parity identity. -/
theorem reflectionUnitary_basis (a : ℝ) (ha : -1<a) (k : ℕ) :
    reflectionUnitary (hilbertBasis a ha k)=(-1:ℝ)^k • hilbertBasis a ha k := by
  -- Every representative is transported only through the genuine measure-preserving original map.
  apply Lp.ext
  filter_upwards [reflectionUnitary_ae (hilbertBasis a ha k),
    unitInterval.measurePreserving_symm.quasiMeasurePreserving.ae_eq_comp (hilbertBasis_ae a ha k),
    hilbertBasis_ae a ha k,Lp.coeFn_smul ((-1:ℝ)^k) (hilbertBasis a ha k)] with t hR hB hV hS
  dsimp only [Function.comp_apply] at hB
  rw [hR,hS]
  change (hilbertBasis a ha k) (unitInterval.symm t)=(-1:ℝ)^k*(hilbertBasis a ha k t)
  rw [hB,hV,unitInterval.coe_symm_eq,eigenfunction_reflection ha]
  ring

/-- The full original half projection, included back into the same full physical L2 space.
Use: its reflection partition proves the half-reference norm and completeness identities.
Article: jacobi, Proposition C.2.
-/
def fullHalfProjection : Space →L[ℝ] Space :=
  halfSubspace.subtypeL ∘L halfSubspace.orthogonalProjectionOnto

/-- The two genuinely reflected half projections partition the original L2 vector.
Use: proves that same-parity full basis pairings are twice their half-interval pairings.
Article: jacobi, Proposition C.2.
Proof: the first projection has the true first-half indicator; transport the second by the original measure-preserving reflection. Off the null midpoint exactly one of the two original indicators contributes. -/
theorem fullHalfProjection_partition (v : Space) :
    fullHalfProjection v+reflectionUnitary (fullHalfProjection (reflectionUnitary v))=v := by
  -- The only overlap of the two closed physical halves is a proved null singleton.
  apply Lp.ext
  have hmid : ∀ᵐ t:Interval,(t:ℝ)≠1/2 := by
    have h := volume.ae_ne (⟨1/2,by norm_num⟩:Interval)
    exact h.mono (fun _ ht he => ht (Subtype.ext he))
  filter_upwards [Lp.coeFn_add (fullHalfProjection v)
      (reflectionUnitary (fullHalfProjection (reflectionUnitary v))),halfProjection_ae v,
    reflectionUnitary_ae (fullHalfProjection (reflectionUnitary v)),
    unitInterval.measurePreserving_symm.quasiMeasurePreserving.ae_eq_comp (halfProjection_ae (reflectionUnitary v)),
    unitInterval.measurePreserving_symm.quasiMeasurePreserving.ae_eq_comp (reflectionUnitary_ae v),hmid]
    with t hAdd hP hR hQ hV ht
  dsimp only [Function.comp_apply] at hQ hV
  rw [hAdd]
  change (halfSubspace.orthogonalProjectionOnto v:Space) t+
    reflectionUnitary (fullHalfProjection (reflectionUnitary v)) t=v t
  rw [hP,hR]
  change (prefixSet (1/2)).indicator v t+
    (halfSubspace.orthogonalProjectionOnto (reflectionUnitary v):Space) (unitInterval.symm t)=v t
  rw [hQ]
  by_cases hp : (t:ℝ)≤1/2
  · rw [indicator_of_mem (show t∈prefixSet (1/2) from hp),
      indicator_of_notMem (show unitInterval.symm t∉prefixSet (1/2) from by
        change ¬(unitInterval.symm t:ℝ)≤1/2
        rw [unitInterval.coe_symm_eq]
        have hlt : (t:ℝ)<1/2 := lt_of_le_of_ne hp ht
        linarith),add_zero]
  · rw [indicator_of_notMem (show t∉prefixSet (1/2) from hp),
      indicator_of_mem (show unitInterval.symm t∈prefixSet (1/2) from by
        change (unitInterval.symm t:ℝ)≤1/2
        rw [unitInterval.coe_symm_eq]
        linarith),zero_add,hV,unitInterval.symm_symm]

end
end jacobi.GelfandLevitan
