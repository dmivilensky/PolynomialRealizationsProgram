import chebyshev2.SineContinuum.LegendreHilbertBasis
import chebyshev2.SineContinuum.LegendreEigenfunctions
import chebyshev2.Continuum.WeightedL2
import chebyshev2.Continuum.MeasureUnitary
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
Article: chebyshev2, Lemma 5.
The true unitary change of variables, initially in shifted Legendre coordinates s=(1-cos(πt))/2.
Use: `chebyshev2.SineContinuum.sineUnitary` feeds
`chebyshev2.SineContinuum.sineUnitary_symm_repr` (sine Unitary symm repr).
Proof chain: `chebyshev2.SineContinuum.legendreV_domain` — chebyshev2, Lemma 5; Legendre
operator, nonlogarithmic realization and continuum sine spectrum.
-/
namespace chebyshev2.SineContinuum
noncomputable section
open Set Real MeasureTheory
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Measure.Subtype.measureSpace

/--
Defines `sineCoordinate` of type `ℝ` by `(1-cos (π*t))/2`.

Use: `chebyshev2.SineContinuum.sineCoordinateIso` uses this definition in the displayed
construction of `sineCoordinateIso`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.
-/
def sineCoordinate (t : ℝ) : ℝ := (1-cos (π*t))/2
/--
Defines `sineJacobian` of type `ℝ` by `(π/2)*sin (π*t)`.

Use: `chebyshev2.SineContinuum.sineCoordinate_derivative` uses this definition to establish
the actual derivative at the stated point: `HasDerivAt sineCoordinate (sineJacobian t) t`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.
-/
def sineJacobian (t : ℝ) : ℝ := (π/2)*sin (π*t)

/--
The actual derivative at the stated point: `HasDerivAt sineCoordinate (sineJacobian t) t`.

Use: `chebyshev2.SineContinuum.sineCoordinate_strictMono` rewrites with this derivative
formula to establish `StrictMonoOn sineCoordinate LegendreInterval`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem sineCoordinate_derivative (t : ℝ) :
    HasDerivAt sineCoordinate (sineJacobian t) t := by
  have h := ((hasDerivAt_const t (1:ℝ)).sub (((hasDerivAt_id t).const_mul π).cos)).div_const 2
  convert h using 1
  · rfl
  · dsimp [sineJacobian]; ring

/--
Exact identity `sineCoordinate 0=0`.

Use: `chebyshev2.SineContinuum.sineCoordinate_surjective` uses this identity to establish
the precise assertion is `SurjOn sineCoordinate LegendreInterval LegendreInterval`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem sineCoordinate_zero : sineCoordinate 0=0 := by simp [sineCoordinate]
/--
Exact identity `sineCoordinate 1=1`.

Use: `chebyshev2.SineContinuum.sineCoordinate_surjective` uses this identity to establish
the precise assertion is `SurjOn sineCoordinate LegendreInterval LegendreInterval`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem sineCoordinate_one : sineCoordinate 1=1 := by simp [sineCoordinate]
/--
Continuity of the displayed function: `Continuous sineCoordinate`.

Use: `chebyshev2.SineContinuum.sineCoordinate_strictMono` uses this continuity result to
establish the precise assertion is `StrictMonoOn sineCoordinate LegendreInterval`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem sineCoordinate_continuous : Continuous sineCoordinate := by unfold sineCoordinate; fun_prop

/--
The stated quantitative bound `0 ≤ sineJacobian t`.

Use: `chebyshev2.SineContinuum.sineWeight_Iic` uses this bound to establish the identity
`sineWeight.measure (Iic t)=ENNReal.ofReal (sineCoordinate t)`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem sineJacobian_nonnegative {t : ℝ} (ht : t ∈ LegendreInterval) : 0 ≤ sineJacobian t :=
  mul_nonneg (by positivity) (sin_nonneg_of_mem_Icc ⟨by nlinarith [pi_pos,ht.1],by nlinarith [pi_pos,ht.2]⟩)

/--
The stated quantitative bound `0 < sineJacobian t`.

Use: `chebyshev2.SineContinuum.sineCoordinate_strictMono` uses this bound to establish the
precise assertion is `StrictMonoOn sineCoordinate LegendreInterval`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem sineJacobian_positive {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) : 0 < sineJacobian t :=
  mul_pos (by positivity) (sin_pos_of_mem_Ioo ⟨by nlinarith [pi_pos,ht.1],by nlinarith [pi_pos,ht.2]⟩)

/--
Membership in the specified domain/enclosure: `sineCoordinate t ∈ LegendreInterval`.

Use: `chebyshev2.SineContinuum.sineCoordinateIso` uses this assertion in the displayed
construction of `sineCoordinateIso`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem sineCoordinate_mem (t : LegendreInterval) : sineCoordinate t ∈ LegendreInterval := by constructor <;> dsimp [sineCoordinate] <;> nlinarith [cos_le_one (π*t),neg_one_le_cos (π*t)]

/--
The precise assertion is `StrictMonoOn sineCoordinate LegendreInterval`.

Use: `chebyshev2.SineContinuum.sineCoordinateIso` uses this assertion in the displayed
construction of `sineCoordinateIso`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.sineCoordinate_continuous`,
`chebyshev2.SineContinuum.sineCoordinate_derivative`,
`chebyshev2.SineContinuum.sineJacobian_positive` with the arguments shown in the proof.
-/
theorem sineCoordinate_strictMono : StrictMonoOn sineCoordinate LegendreInterval := by
  apply strictMonoOn_of_deriv_pos (convex_Icc (0:ℝ) 1) sineCoordinate_continuous.continuousOn
  intro t ht
  rw [interior_Icc] at ht
  rw [(sineCoordinate_derivative t).deriv]
  exact sineJacobian_positive ht

/--
The precise assertion is `SurjOn sineCoordinate LegendreInterval LegendreInterval`.

Use: `chebyshev2.SineContinuum.sineCoordinateIso` uses this assertion in the displayed
construction of `sineCoordinateIso`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.sineCoordinate_continuous`,
`chebyshev2.SineContinuum.sineCoordinate_zero`,
`chebyshev2.SineContinuum.sineCoordinate_one` with the arguments shown in the proof.
-/
theorem sineCoordinate_surjective : SurjOn sineCoordinate LegendreInterval LegendreInterval := by
  have h := sineCoordinate_continuous.continuousOn.surjOn_Icc
    (s := LegendreInterval) (a := 0) (b := 1) (by norm_num) (by norm_num)
  simpa only [sineCoordinate_zero,sineCoordinate_one] using h

/--
Defines `sineCoordinateIso` of type `LegendreInterval ≃o LegendreInterval` by
`StrictMono.orderIsoOfSurjective (fun t => ⟨sineCoordinate t,sineCoordinate_mem t⟩) (fun a b
hab => sineCoordinate_strictMono a.property b.property hab) (fun y => by obtain ⟨x,hx,he⟩ :=
sineCoordinate_surjective y.property exact ⟨⟨x,hx⟩,Subtype.ext he⟩)`.

Use: `chebyshev2.SineContinuum.sineCoordinateEquiv` uses this definition in the displayed
construction of `sineCoordinateEquiv`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.
-/
def sineCoordinateIso : LegendreInterval ≃o LegendreInterval :=
  StrictMono.orderIsoOfSurjective (fun t => ⟨sineCoordinate t,sineCoordinate_mem t⟩)
    (fun a b hab => sineCoordinate_strictMono a.property b.property hab)
    (fun y => by
      obtain ⟨x,hx,he⟩ := sineCoordinate_surjective y.property
      exact ⟨⟨x,hx⟩,Subtype.ext he⟩)

/--
Exact identity `(sineCoordinateIso t:ℝ)=sineCoordinate t`.

Use: `chebyshev2.SineContinuum.legendreV_ae` uses this identity to establish the identity
`legendreV f=ᵐ[volume] (fun t : LegendreInterval => √(π*sin (π*(t:ℝ)))*f (cosineInterval t))`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem sineCoordinateIso_apply (t : LegendreInterval) :
    (sineCoordinateIso t:ℝ)=sineCoordinate t :=
  congrArg Subtype.val (congrFun (StrictMono.coe_orderIsoOfSurjective _ _ _) t)

/--
Defines `sineCoordinateEquiv` of type `LegendreInterval ≃ᵐ LegendreInterval` by
`sineCoordinateIso.toHomeomorph.toMeasurableEquiv`.

Use: `chebyshev2.SineContinuum.sineCoordinate_measurePreserving` rewrites with this
definition to establish `MeasurePreserving sineCoordinateEquiv
sineWeight.measure volume`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.
-/
def sineCoordinateEquiv : LegendreInterval ≃ᵐ LegendreInterval :=
  sineCoordinateIso.toHomeomorph.toMeasurableEquiv

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ t : LegendreInterval
∂volume, (t:ℝ) ∈ Ioo (0:ℝ) 1`.

Use: `chebyshev2.SineContinuum.sineWeight` uses this assertion in the displayed
construction of `sineWeight`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem interval_interior_ae : ∀ᵐ t : LegendreInterval ∂volume, (t:ℝ) ∈ Ioo (0:ℝ) 1 := by
  filter_upwards [volume.ae_ne (0:LegendreInterval),volume.ae_ne (1:LegendreInterval)] with t h0 h1
  constructor
  · exact lt_of_le_of_ne t.property.1 (fun h => h0 (Subtype.ext h.symm))
  · exact lt_of_le_of_ne t.property.2 (fun h => h1 (Subtype.ext h))

/--
Constructs `sineWeight` of type `Continuum.L2Weight (volume : Measure LegendreInterval)` by the
displayed record fields. Data fields specify the construction; proof fields discharge its
required properties.

Use: `chebyshev2.SineContinuum.sineUnitary` uses this definition in the displayed
construction of `sineUnitary`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.
-/
def sineWeight : Continuum.L2Weight (volume : Measure LegendreInterval) where
  w t := √(sineJacobian t)
  measurable := by dsimp [sineJacobian]; fun_prop
  nonzero := by
    filter_upwards [interval_interior_ae] with t ht
    exact (sqrt_pos.mpr (sineJacobian_positive ht)).ne'

/--
Exact identity `sineWeight.density t=ENNReal.ofReal (sineJacobian t)`.

Use: `chebyshev2.SineContinuum.sineWeight_Iic` rewrites with this identity to establish
exact identity `sineWeight.measure (Iic t)=ENNReal.ofReal (sineCoordinate t)`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.sineJacobian_nonnegative`
with the arguments shown in the proof.
-/
theorem sineWeight_density (t : LegendreInterval) :
    sineWeight.density t=ENNReal.ofReal (sineJacobian t) :=
  congrArg ENNReal.ofReal (sq_sqrt (sineJacobian_nonnegative t.property))

/--
Exact identity `sineWeight.measure (Iic t)=ENNReal.ofReal (sineCoordinate t)`.

Use: `chebyshev2.SineContinuum.sineCoordinate_measurePreserving` rewrites with this
identity to establish `MeasurePreserving sineCoordinateEquiv
sineWeight.measure volume`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem sineWeight_Iic (t : LegendreInterval) :
    sineWeight.measure (Iic t)=ENNReal.ofReal (sineCoordinate t) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  rw [Continuum.L2Weight.measure,withDensity_apply _ measurableSet_Iic]
  simp only [sineWeight_density]
  change (∫⁻ a in Iic t, ENNReal.ofReal (sineJacobian (a:ℝ)) ∂volume.comap ((↑) : LegendreInterval → ℝ))=_
  rw [setLIntegral_subtype measurableSet_Icc (Iic t) (fun x : ℝ => ENNReal.ofReal (sineJacobian x)),image_subtype_val_Icc_Iic]
  have hd : IntervalIntegrable sineJacobian volume 0 t := by
    exact (by unfold sineJacobian; fun_prop : Continuous sineJacobian).intervalIntegrable 0 t
  rw [← ofReal_integral_eq_lintegral_ofReal ((intervalIntegrable_iff_integrableOn_Icc_of_le t.property.1).mp hd)]
  · rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le t.property.1]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => sineCoordinate_derivative x)
      hd,sineCoordinate_zero,sub_zero]
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact sineJacobian_nonnegative ⟨hx.1,hx.2.trans t.property.2⟩

/--
Supplies the typeclass structure specified by `IsFiniteMeasure sineWeight.measure`. This lets
subsequent generic library results apply to this concrete type.

Use: `chebyshev2.SineContinuum.sineCoordinate_measurePreserving` uses this typeclass
instance to establish `MeasurePreserving sineCoordinateEquiv
sineWeight.measure volume`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.sineWeight_Iic` with the
arguments shown in the proof.
-/
instance sineWeight_finiteMeasure : IsFiniteMeasure sineWeight.measure := by
  constructor
  have he : (Iic (1:LegendreInterval))=univ := by ext x; simp only [mem_Iic,mem_univ,iff_true]; exact x.property.2
  rw [← he,sineWeight_Iic]
  simp [sineCoordinate]

/--
Exact Jacobian pushforward, including the null endpoints.

The precise assertion is `MeasurePreserving sineCoordinateEquiv sineWeight.measure volume`.

Use: `chebyshev2.SineContinuum.sineUnitary` uses this assertion in the displayed
construction of `sineUnitary`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.sineWeight_Iic` with the
arguments shown in the proof.
-/
theorem sineCoordinate_measurePreserving :
    MeasurePreserving sineCoordinateEquiv sineWeight.measure volume := by
  -- Use the identities/estimates `chebyshev2.SineContinuum.sineWeight_Iic` with the
  -- arguments shown in the proof.
  constructor
  · exact sineCoordinateEquiv.measurable
  · apply Measure.ext_of_Iic
    intro t
    rw [Measure.map_apply sineCoordinateEquiv.measurable measurableSet_Iic]
    have he : sineCoordinateEquiv ⁻¹' Iic t=Iic (sineCoordinateIso.symm t) := by
      ext x
      change sineCoordinateIso x ≤ t ↔ x ≤ sineCoordinateIso.symm t
      exact sineCoordinateIso.le_symm_apply.symm
    rw [he,sineWeight_Iic,unitInterval.volume_Iic]
    have hx := sineCoordinateIso.apply_symm_apply t
    exact congrArg (fun x : LegendreInterval => ENNReal.ofReal (x:ℝ)) hx

/--
The true unitary change of variables, initially in shifted Legendre coordinates
s=(1-cos(πt))/2.

Use: `chebyshev2.SineContinuum.legendreV` uses this definition in the displayed
construction of `legendreV`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.
-/
def sineUnitary : LegendreSpace ≃ₗᵢ[ℝ] LegendreSpace :=
  (Continuum.measureUnitary sineCoordinateEquiv sineCoordinate_measurePreserving).trans sineWeight.equiv

end
end chebyshev2.SineContinuum
