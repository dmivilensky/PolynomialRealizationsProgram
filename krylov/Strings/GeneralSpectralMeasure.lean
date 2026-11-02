import krylov.Strings.GeneralSpectralResolvent
import krylov.Strings.GeneralSpectralTents

/-!
Article: main_krylov, apC:prop:tauber, the actual principal measure.
Use: construct a probability boundary spectral measure for arbitrary total
mass and identify its positive-parameter Stieltjes transform with the actual
physical weak resolvent. Local finite-prefix tents exclude an infinite-energy
boundary component. No representation identity is supplied as a certificate.
Source: the genuine Neumann energy graph, CFC/RMK and the resolvent identity.
-/

namespace krylov.Strings.GeneralSpectral
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContinuousFunctionalCalculus
variable (S : StringMeasure)

/-- The genuine unit-resolvent scalar spectral measure at the physical atom. -/
def resolventMeasure : Measure (spectrum ℝ (neumannResolvent S)) :=
  Spectral.scalarMeasure (neumannResolvent S) (neumannResolvent_selfAdjoint S) (boundaryVector S)

instance resolventMeasure_probability : IsProbabilityMeasure (resolventMeasure S) :=
  Spectral.scalarMeasure_probability _ _ (boundaryVector_norm S)

/-- The actual spectral coordinate from resolvent to physical string energy. -/
def spectralParameter (u : spectrum ℝ (neumannResolvent S)) : ℝ := (u : ℝ)⁻¹ - 1

/-- The true reciprocal spectral coordinate is measurable. -/
theorem spectralParameter_measurable : Measurable (spectralParameter S) :=
  continuous_subtype_val.measurable.inv.sub measurable_const

/-- The principal boundary measure of the constructed physical energy realization. -/
def principalMeasure : Measure ℝ := (resolventMeasure S).map (spectralParameter S)

instance principalMeasure_probability : IsProbabilityMeasure (principalMeasure S) := by
  unfold principalMeasure
  infer_instance

/-- Actual finite-energy tents remove any scalar spectral atom at zero for
the bounded resolvent, without requiring finite total string mass. -/
theorem resolventMeasure_zero (N : ℕ) (hf : S.measure (Icc 0 (Spectral.tentScale N)) ≠ ⊤)
    (hphysical : S.measure (Iio 0) = 0) :
    resolventMeasure S {u | (u : ℝ) = 0} = 0 := by
  have h := Spectral.scalarMeasure_zero_atom (neumannResolvent S)
    (neumannResolvent_selfAdjoint S) (neumannResolvent_complement_norm_le S) (boundaryVector S)
  have ho : boundaryVector S ∈ (neumannResolvent S).kerᗮ := by
    apply ((neumannResolvent S).ker.mem_orthogonal _).mpr
    intro v hv
    have hh := neumann_kernel_boundary_inner S N hf hphysical (show neumannResolvent S v = 0 from hv)
    rw [← inner_conj_symm, hh, map_zero]
  have hp : (neumannResolvent S).ker.starProjection (boundaryVector S) = 0 := by
    rw [← (neumannResolvent S).ker.ker_starProjection] at ho
    exact ho
  have hn : ‖(neumannResolvent S).ker.orthogonalProjectionOnto (boundaryVector S)‖ = 0 := by
    change ‖(neumannResolvent S).ker.starProjection (boundaryVector S)‖ = 0
    rw [hp, norm_zero]
  rw [hn, zero_pow (by norm_num : (2 : ℕ) ≠ 0), ENNReal.ofReal_zero] at h
  exact h

/-- The actual principal probability measure is carried by nonnegative
physical energies, including singular strings of infinite total mass. -/
theorem principalMeasure_negative (N : ℕ) (hf : S.measure (Icc 0 (Spectral.tentScale N)) ≠ ⊤)
    (hphysical : S.measure (Iio 0) = 0) : principalMeasure S (Iio 0) = 0 := by
  rw [principalMeasure, Measure.map_apply (spectralParameter_measurable S) measurableSet_Iio]
  have he : spectralParameter S ⁻¹' Iio 0 = {u : spectrum ℝ (neumannResolvent S) | (u : ℝ) = 0} := by
    ext u
    change (u : ℝ)⁻¹ - 1 < 0 ↔ (u : ℝ) = 0
    obtain ⟨h0, h1⟩ := neumannResolvent_spectrum_bounds S u.property
    by_cases hz : (u : ℝ) = 0
    · simp [hz]
    · have hp : 0 < (u : ℝ) := lt_of_le_of_ne h0 (Ne.symm hz)
      have hi : 1 ≤ (u : ℝ)⁻¹ := (one_le_inv₀ hp).2 h1
      constructor
      · intro h
        linarith
      · exact fun h ↦ (hz h).elim
  rw [he, resolventMeasure_zero S N hf hphysical]

/-- The actual physical boundary compliance at positive energy. -/
def boundaryCompliance (t : ℝ) (ht : 0 < t) : ℝ :=
  (inner ℂ (boundaryVector S) (parameterResolvent S t ht (boundaryVector S))).re

private theorem resolventFunction_integrable (t : ℝ) (ht : 0 < t) :
    Integrable (resolventFunction S t ht) (resolventMeasure S) := by
  have : CompactSpace (spectrum ℝ (neumannResolvent S)) :=
    isCompact_iff_compactSpace.mp (spectrum.isCompact (neumannResolvent S))
  simpa only [IntegrableOn, Measure.restrict_univ] using
    (resolventFunction S t ht).continuous.continuousOn.integrableOn_compact
      (μ := resolventMeasure S) isCompact_univ

private theorem reciprocal_ae (N : ℕ) (hf : S.measure (Icc 0 (Spectral.tentScale N)) ≠ ⊤)
    (hphysical : S.measure (Iio 0) = 0) (t : ℝ) (ht : 0 < t) :
    (fun u ↦ 1 / (spectralParameter S u + t)) =ᵐ[resolventMeasure S] resolventFunction S t ht := by
  have hae : ∀ᵐ u : spectrum ℝ (neumannResolvent S) ∂(resolventMeasure S), (u : ℝ) ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using resolventMeasure_zero S N hf hphysical
  filter_upwards [hae] with u hu
  change 1 / ((u : ℝ)⁻¹ - 1 + t) = (u : ℝ) / (1 + (t - 1) * (u : ℝ))
  field_simp [hu, (resolventDenominator_pos S ht u).ne']
  ring

/-- The actual principal measure has an integrable Stieltjes kernel at
every positive energy, proved from the compact spectral calculus. -/
theorem principalMeasure_stieltjes_integrable (N : ℕ)
    (hf : S.measure (Icc 0 (Spectral.tentScale N)) ≠ ⊤) (hphysical : S.measure (Iio 0) = 0)
    (t : ℝ) (ht : 0 < t) : Integrable (fun ξ : ℝ ↦ 1 / (ξ + t)) (principalMeasure S) := by
  have hm : Measurable (fun ξ : ℝ ↦ 1 / (ξ + t)) := by fun_prop
  change Integrable _ ((resolventMeasure S).map (spectralParameter S))
  apply (integrable_map_measure hm.aestronglyMeasurable (spectralParameter_measurable S).aemeasurable).2
  exact (resolventFunction_integrable S t ht).congr (reciprocal_ae S N hf hphysical t ht).symm

/-- The actual scalar principal Stieltjes transform equals the actual
physical weak Neumann compliance for every positive parameter. -/
theorem principalMeasure_stieltjes (N : ℕ) (hf : S.measure (Icc 0 (Spectral.tentScale N)) ≠ ⊤)
    (hphysical : S.measure (Iio 0) = 0) (t : ℝ) (ht : 0 < t) :
    (∫ ξ : ℝ, 1 / (ξ + t) ∂principalMeasure S) = boundaryCompliance S t ht := by
  have hm : Measurable (fun ξ : ℝ ↦ 1 / (ξ + t)) := by fun_prop
  rw [principalMeasure, integral_map (spectralParameter_measurable S).aemeasurable hm.aestronglyMeasurable]
  rw [integral_congr_ae (reciprocal_ae S N hf hphysical t ht)]
  exact Spectral.integral_operatorCalculus _ _ _ _

/-- The weighted Stieltjes defect of the actual probability measure is
one minus t times the actual physical boundary compliance. -/
theorem principalMeasure_defect (N : ℕ) (hf : S.measure (Icc 0 (Spectral.tentScale N)) ≠ ⊤)
    (hphysical : S.measure (Iio 0) = 0) (t : ℝ) (ht : 0 < t) :
    (∫ ξ : ℝ, ξ / (ξ + t) ∂principalMeasure S) = 1 - t * boundaryCompliance S t ht := by
  have hn : ∀ᵐ ξ ∂principalMeasure S, 0 ≤ ξ := by
    rw [ae_iff]
    simpa only [not_le, Iio] using principalMeasure_negative S N hf hphysical
  have he : (fun ξ : ℝ ↦ ξ / (ξ + t)) =ᵐ[principalMeasure S] (fun ξ ↦ 1 - t * (1 / (ξ + t))) := by
    filter_upwards [hn] with ξ hξ
    field_simp [(add_pos_of_nonneg_of_pos hξ ht).ne']
    ring
  rw [integral_congr_ae he, integral_sub (integrable_const 1)
    ((principalMeasure_stieltjes_integrable S N hf hphysical t ht).const_mul t), integral_const_mul,
    principalMeasure_stieltjes S N hf hphysical t ht]
  simp

end
end krylov.Strings.GeneralSpectral
