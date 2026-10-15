import «2610.05164v2».SineContinuum.NoLogarithm
import «2610.05164v2».SineContinuum.RealLineUnitary

/-!
Article: 2610.05164v2, Lemma 5.
The actual affine unitary from L²(-1,1) to the shifted interval: it is sqrt(2) times f(1-2s).
Use: `«2610.05164v2».SineContinuum.affineLegendreUnitary` feeds
`«2610.05164v2».SineContinuum.affineLegendre_domain` (affine Legendre domain).
Proof chain: `«2610.05164v2».SineContinuum.legendreV_domain` — 2610.05164v2, Lemma 5; Legendre
operator, nonlogarithmic realization and continuum sine spectrum.
-/
namespace «2610.05164v2».SineContinuum
noncomputable section
open Set Real MeasureTheory
open scoped ENNReal
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency true

/--
Defines `StandardInterval` of type `` by `Icc (-1:ℝ) 1`.

Use: `«2610.05164v2».SineContinuum.StandardSpace` uses this definition in the displayed
construction of `StandardSpace`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Lemma 5 via `«2610.05164v2».SineContinuum.legendreV_domain`.
-/
abbrev StandardInterval := Icc (-1:ℝ) 1
/--
Defines `StandardSpace` of type `` by `Lp ℝ 2 (volume : Measure StandardInterval)`.

Use: `«2610.05164v2».SineContinuum.affineLegendreUnitary` uses this definition in the displayed
construction of `affineLegendreUnitary`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Lemma 5 via `«2610.05164v2».SineContinuum.legendreV_domain`.
-/
abbrev StandardSpace := Lp ℝ 2 (volume : Measure StandardInterval)

/--
Supplies the typeclass structure specified by `IsFiniteMeasure (volume : Measure
StandardInterval)`. This lets subsequent generic library results apply to this concrete type.

Use: `«2610.05164v2».SineContinuum.standardWeight_finiteMeasure` uses this typeclass instance
in the displayed construction of `standardWeight_finiteMeasure`. Its inputs and component
formulas are fixed by that definition.

Article: 2610.05164v2, Lemma 5.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
instance standardInterval_finiteMeasure : IsFiniteMeasure (volume : Measure StandardInterval) := by
  constructor
  change volume.comap ((↑) : StandardInterval → ℝ) univ < ⊤
  rw [Measure.comap_apply ((↑) : StandardInterval → ℝ) ((MeasurableEmbedding.subtype_coe measurableSet_Icc).injective)
    (MeasurableEmbedding.subtype_coe measurableSet_Icc).measurableSet_image' volume MeasurableSet.univ]
  rw [image_univ,Subtype.range_coe]
  exact isCompact_Icc.measure_lt_top

/--
Defines `affineLegendreEquiv` of type `LegendreInterval ≃ᵐ StandardInterval`. The displayed
construction fixes its component data; its proof fields enforce the listed compatibility
properties.

Use: `«2610.05164v2».SineContinuum.affineLegendreUnitary` uses this definition in the displayed
construction of `affineLegendreUnitary`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Lemma 5 via `«2610.05164v2».SineContinuum.legendreV_domain`.
-/
def affineLegendreEquiv : LegendreInterval ≃ᵐ StandardInterval :=
  Homeomorph.toMeasurableEquiv {
    toEquiv := {
      toFun t := ⟨1-2*(t:ℝ),by constructor <;> linarith [t.property.1,t.property.2]⟩
      invFun z := ⟨(1-(z:ℝ))/2,by constructor <;> linarith [z.property.1,z.property.2]⟩
      left_inv t := by apply Subtype.ext; dsimp; ring
      right_inv z := by apply Subtype.ext; dsimp; ring }
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }

/--
Constructs `standardWeight` of type `Continuum.L2Weight (volume : Measure StandardInterval)` by
the displayed record fields. Data fields specify the construction; proof fields discharge its
required properties.

Use: `«2610.05164v2».SineContinuum.affineLegendreUnitary` uses this definition in the displayed
construction of `affineLegendreUnitary`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Lemma 5 via `«2610.05164v2».SineContinuum.legendreV_domain`.
-/
def standardWeight : Continuum.L2Weight (volume : Measure StandardInterval) where
  w _ := √(1/2:ℝ)
  measurable := measurable_const
  nonzero := Filter.Eventually.of_forall (fun _ => (sqrt_pos.mpr (by norm_num : (0:ℝ)<1/2)).ne')

/--
Exact identity `standardWeight.measure=ENNReal.ofReal (1/2:ℝ) • (volume : Measure
StandardInterval)`.

Use: `«2610.05164v2».SineContinuum.affineLegendre_measurePreserving` rewrites with this
identity to establish `MeasurePreserving affineLegendreEquiv (volume :
Measure LegendreInterval) standardWeight.measure`.

Article: 2610.05164v2, Lemma 5 via `«2610.05164v2».SineContinuum.legendreV_domain`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem standardWeight_measure :
    standardWeight.measure=ENNReal.ofReal (1/2:ℝ) • (volume : Measure StandardInterval) := by
  change (volume : Measure StandardInterval).withDensity (fun _ => ENNReal.ofReal ((√(1/2:ℝ))^2))=_
  rw [sq_sqrt (by norm_num : (0:ℝ) ≤ 1/2),withDensity_const]

/--
Supplies the typeclass structure specified by `IsFiniteMeasure standardWeight.measure`. This
lets subsequent generic library results apply to this concrete type.

Use: supplies this typeclass to generic library results in the module; instance resolution
inserts it where required by their signatures.

Article: 2610.05164v2, Lemma 5.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.standardWeight_measure` with
the arguments shown in the proof.
-/
instance standardWeight_finiteMeasure : IsFiniteMeasure standardWeight.measure := by
  constructor
  rw [standardWeight_measure,Measure.smul_apply]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

/--
The precise assertion is `MeasurePreserving affineLegendreEquiv (volume : Measure
LegendreInterval) standardWeight.measure`.

Use: `«2610.05164v2».SineContinuum.affineLegendreUnitary` uses this assertion in the displayed
construction of `affineLegendreUnitary`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Lemma 5 via `«2610.05164v2».SineContinuum.legendreV_domain`.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.standardWeight_measure` with
the arguments shown in the proof.
-/
theorem affineLegendre_measurePreserving :
    MeasurePreserving affineLegendreEquiv (volume : Measure LegendreInterval) standardWeight.measure := by
  -- Use the identities/estimates `«2610.05164v2».SineContinuum.standardWeight_measure` with
  -- the arguments shown in the proof.
  constructor
  · exact affineLegendreEquiv.measurable
  · apply Measure.ext_of_Iic
    intro z
    rw [Measure.map_apply affineLegendreEquiv.measurable measurableSet_Iic,standardWeight_measure,
      Measure.smul_apply]
    change (volume.comap ((↑) : LegendreInterval → ℝ)) (affineLegendreEquiv ⁻¹' Iic z)=
      ENNReal.ofReal (1/2:ℝ)*(volume.comap ((↑) : StandardInterval → ℝ)) (Iic z)
    rw [Measure.comap_apply ((↑) : LegendreInterval → ℝ) (MeasurableEmbedding.subtype_coe measurableSet_Icc).injective
      (MeasurableEmbedding.subtype_coe measurableSet_Icc).measurableSet_image' volume
      (affineLegendreEquiv.measurable measurableSet_Iic),
      Measure.comap_apply ((↑) : StandardInterval → ℝ) (MeasurableEmbedding.subtype_coe measurableSet_Icc).injective
      (MeasurableEmbedding.subtype_coe measurableSet_Icc).measurableSet_image' volume measurableSet_Iic,
      image_subtype_val_Icc_Iic]
    have he : ((↑) : LegendreInterval → ℝ) '' (affineLegendreEquiv ⁻¹' Iic z)=
        Icc ((1-(z:ℝ))/2) 1 := by
      ext t
      constructor
      · rintro ⟨u,hu,rfl⟩
        change 1-2*(u:ℝ) ≤ (z:ℝ) at hu
        exact ⟨by linarith,u.property.2⟩
      · intro ht
        have h0 : 0 ≤ t := by linarith [z.property.2,ht.1]
        refine ⟨⟨t,⟨h0,ht.2⟩⟩,?_,rfl⟩
        change 1-2*t ≤ (z:ℝ)
        linarith [ht.1]
    rw [he,Real.volume_Icc,Real.volume_Icc,← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤1/2)]
    congr 1
    ring

/--
The actual affine unitary from L²(-1,1) to the shifted interval: it is sqrt(2) times f(1-2s).

Use: `«2610.05164v2».SineContinuum.affineLegendreUnitary_ae` uses this definition to establish
exact identity `affineLegendreUnitary f=ᵐ[volume] (fun t : LegendreInterval => f
(affineLegendreEquiv t)/√(1/2:ℝ))`.

Article: 2610.05164v2, Lemma 5 via `«2610.05164v2».SineContinuum.legendreV_domain`.
-/
def affineLegendreUnitary : StandardSpace ≃ₗᵢ[ℝ] LegendreSpace :=
  standardWeight.equiv.symm.trans
    (Continuum.measureUnitary affineLegendreEquiv affineLegendre_measurePreserving)

/--
Exact identity `standardWeight.equiv.symm f=ᵐ[standardWeight.measure] (fun z => f z/√(1/2:ℝ))`.

Use: `«2610.05164v2».SineContinuum.affineLegendreUnitary_ae` uses this identity to establish
exact identity `affineLegendreUnitary f=ᵐ[volume] (fun t : LegendreInterval => f
(affineLegendreEquiv t)/√(1/2:ℝ))`.

Article: 2610.05164v2, Lemma 5.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem standardWeight_inverse_ae (f : StandardSpace) :
    standardWeight.equiv.symm f=ᵐ[standardWeight.measure]
      (fun z => f z/√(1/2:ℝ)) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  apply standardWeight.weight_ac.ae_eq
  have h := standardWeight.mul_ae (standardWeight.equiv.symm f)
  have he : standardWeight.mul (standardWeight.equiv.symm f)=f :=
    standardWeight.equiv.apply_symm_apply f
  rw [he] at h
  filter_upwards [h] with z hz
  apply (eq_div_iff (sqrt_pos.mpr (by norm_num : (0:ℝ)<1/2)).ne').mpr
  simpa only [standardWeight,mul_comm] using hz.symm

/--
Exact identity `affineLegendreUnitary f=ᵐ[volume] (fun t : LegendreInterval => f
(affineLegendreEquiv t)/√(1/2:ℝ))`.

Use: `«2610.05164v2».SineContinuum.legendreV_ae` uses this identity to establish the identity
`legendreV f=ᵐ[volume] (fun t : LegendreInterval => √(π*sin (π*(t:ℝ)))*f (cosineInterval t))`.

Article: 2610.05164v2, Lemma 5.

Proof: Use the identities/estimates
`«2610.05164v2».SineContinuum.affineLegendre_measurePreserving`,
`«2610.05164v2».SineContinuum.standardWeight_inverse_ae`,
`«2610.05164v2».Continuum.measureUnitary_ae` with the arguments shown in the proof.
-/
theorem affineLegendreUnitary_ae (f : StandardSpace) :
    affineLegendreUnitary f=ᵐ[volume]
      (fun t : LegendreInterval => f (affineLegendreEquiv t)/√(1/2:ℝ)) := by
  have h := affineLegendre_measurePreserving.quasiMeasurePreserving.ae_eq_comp
    (standardWeight_inverse_ae f)
  exact (Continuum.measureUnitary_ae affineLegendreEquiv affineLegendre_measurePreserving
    (standardWeight.equiv.symm f)).trans h

/--
Exact identity `affineLegendreUnitary.symm f=ᵐ[volume] (fun z : StandardInterval => √(1/2:ℝ)*f
(affineLegendreEquiv.symm z))`.

Use: `«2610.05164v2».SineContinuum.standardLegendreHilbertBasis_ae` uses this identity to
establish exact identity `standardLegendreHilbertBasis j=ᵐ[volume] (fun z : StandardInterval =>
√((j:ℝ)+1/2)*legendre j z)`.

Article: 2610.05164v2, Lemma 5.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Prove equality of functions by evaluating both
sides at an arbitrary argument.
-/
theorem affineLegendreUnitary_symm_ae (f : LegendreSpace) :
    affineLegendreUnitary.symm f=ᵐ[volume]
      (fun z : StandardInterval => √(1/2:ℝ)*f (affineLegendreEquiv.symm z)) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  let g := Continuum.measureUnitary affineLegendreEquiv affineLegendre_measurePreserving
  have hi : g.symm f=Lp.compMeasurePreserving affineLegendreEquiv.symm
      (affineLegendre_measurePreserving.symm affineLegendreEquiv) f := by
    apply g.injective
    rw [g.apply_symm_apply]
    change f=Lp.compMeasurePreserving affineLegendreEquiv affineLegendre_measurePreserving
      (Lp.compMeasurePreserving affineLegendreEquiv.symm
        (affineLegendre_measurePreserving.symm affineLegendreEquiv) f)
    rw [← Lp.compMeasurePreserving_comp_apply]
    have he : (affineLegendreEquiv.symm ∘ affineLegendreEquiv)=id :=
      funext affineLegendreEquiv.symm_apply_apply
    simp only [he,Lp.compMeasurePreserving_id_apply]
  have hc := standardWeight.base_ac.ae_eq (Lp.coeFn_compMeasurePreserving f
    (affineLegendre_measurePreserving.symm affineLegendreEquiv))
  have hm := standardWeight.mul_ae (g.symm f)
  rw [hi] at hm
  filter_upwards [hm,hc] with z hm hc
  change standardWeight.mul (g.symm f) z=_
  rw [hi,hm,hc]
  rfl

end
end «2610.05164v2».SineContinuum
