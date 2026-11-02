import krylov.Strings.SpectralEnergy
import krylov.Strings.SpectralAtom
import krylov.Strings.SpectralTentKernel

/-!
Article: `main_krylov`, `thm:value`, the principal boundary spectral measure.
Construct the actual scalar spectral measure of the Neumann energy resolvent
at the unit origin vector, then use the spectral coordinate λ=t⁻¹−1.
The zero eigenatom is computed from the actual constant eigenspace and the
actual full Stieltjes mass. No atom formula is assumed in the construction.
Source: the bounded resolvent version of the standard principal spectral
measure of a free-left-end string; scalar CFC and RMK supply its construction.
-/

namespace krylov.Strings.Spectral
noncomputable section
open Set MeasureTheory
open scoped Topology ContinuousFunctionalCalculus Pointwise

variable (M : Mass) [IsFiniteMeasure M.measure]

/-- The actual scalar spectral measure of the constructed string resolvent. -/
def resolventMeasure : Measure (spectrum ℝ (neumannResolvent M)) :=
  scalarMeasure (neumannResolvent M) (neumannResolvent_selfAdjoint M) (boundaryVector M)

instance resolventMeasure_probability : IsProbabilityMeasure (resolventMeasure M) :=
  scalarMeasure_probability _ _ (boundaryVector_norm M)

/-- The resolvent spectral parameter is genuinely in `[0,1]`. -/
theorem neumannResolvent_spectrum_bounds {r : ℝ} (hr : r ∈ spectrum ℝ (neumannResolvent M)) :
    0 ≤ r ∧ r ≤ 1 := by
  have hnorm : |r| ≤ 1 := (spectrum.norm_le_norm_of_mem hr).trans
    (neumannResolvent_norm_le M)
  have hmem : 1 - r ∈ spectrum ℝ (1 - neumannResolvent M) := by
    have he : 1 - r ∈ spectrum ℝ
        (algebraMap ℝ (MassHilbert M →L[ℂ] MassHilbert M) 1 - neumannResolvent M) := by
      rw [← spectrum.singleton_sub_eq]
      exact ⟨1, mem_singleton 1, r, hr, rfl⟩
    simpa only [map_one] using he
  have hcomp : |1 - r| ≤ 1 := (spectrum.norm_le_norm_of_mem hmem).trans
    (neumannResolvent_complement_norm_le M)
  constructor
  · linarith [(le_abs_self (1 - r)).trans hcomp]
  · exact (le_abs_self r).trans hnorm

/-- The spectral coordinate taking `(I+A)⁻¹` back to the string energy. -/
def spectralParameter (t : spectrum ℝ (neumannResolvent M)) : ℝ := (t : ℝ)⁻¹ - 1

theorem spectralParameter_measurable : Measurable (spectralParameter M) :=
  continuous_subtype_val.measurable.inv.sub measurable_const

/-- The principal boundary measure, constructed from the true Neumann energy
realization and the actual unit left atom. -/
def principalMeasure : Measure ℝ := (resolventMeasure M).map (spectralParameter M)

instance principalMeasure_probability : IsProbabilityMeasure (principalMeasure M) := by
  unfold principalMeasure
  infer_instance

/-- The true fixed eigenatom of the resolvent is reciprocal full mass. -/
theorem resolventMeasure_one : resolventMeasure M {t | (t : ℝ) = 1} =
    ENNReal.ofReal (M.measure.real univ)⁻¹ := by
  have h := scalarMeasure_fixed_atom (neumannResolvent M)
    (neumannResolvent_selfAdjoint M) (neumannResolvent_norm_le M) (boundaryVector M)
  have hn : ‖((neumannResolvent M).eqLocus (1 : MassHilbert M →L[ℂ] MassHilbert M)).orthogonalProjectionOnto
        (boundaryVector M)‖ =
      ‖(ℂ ∙ constantVector M).orthogonalProjectionOnto (boundaryVector M)‖ := by
    have hc : ∀ K L : Submodule ℂ (MassHilbert M),
        ∀ [K.HasOrthogonalProjection] [L.HasOrthogonalProjection], K = L →
        ‖K.orthogonalProjectionOnto (boundaryVector M)‖ =
          ‖L.orthogonalProjectionOnto (boundaryVector M)‖ := by
      intro K L _ _ he
      subst L
      rfl
    exact hc _ _ (neumannResolvent_fixed_space M)
  rw [hn, constant_projection_weight] at h
  exact h

/-- The physical boundary vector has no zero-resolvent spectral mass. This
uses actual shrinking finite-energy tents, so no density hypothesis is needed. -/
theorem resolventMeasure_zero : resolventMeasure M {t | (t : ℝ) = 0} = 0 := by
  have h := scalarMeasure_zero_atom (neumannResolvent M)
    (neumannResolvent_selfAdjoint M) (neumannResolvent_complement_norm_le M) (boundaryVector M)
  have hn : ‖(neumannResolvent M).ker.orthogonalProjectionOnto (boundaryVector M)‖ = 0 := by
    change ‖(neumannResolvent M).ker.starProjection (boundaryVector M)‖ = 0
    rw [boundary_neumann_kernel_projection_zero, norm_zero]
  rw [hn, zero_pow (by norm_num : (2 : ℕ) ≠ 0), ENNReal.ofReal_zero] at h
  exact h

/-- The atom of the actual principal boundary spectral measure at zero is
the reciprocal actual total mass, including the distinguished origin atom. -/
theorem principalMeasure_zero : principalMeasure M {0} =
    ENNReal.ofReal (M.measure.real univ)⁻¹ := by
  rw [principalMeasure, Measure.map_apply (spectralParameter_measurable M)
    (measurableSet_singleton 0)]
  have hs : spectralParameter M ⁻¹' {0} =
      {t : spectrum ℝ (neumannResolvent M) | (t : ℝ) = 1} := by
    ext t
    simp only [mem_preimage, mem_singleton_iff, spectralParameter, sub_eq_zero, inv_eq_one]
    rfl
  rw [hs, resolventMeasure_one]

/-- The constructed principal string measure is carried by nonnegative
energies. The reciprocal spectral coordinate introduces no negative atom. -/
theorem principalMeasure_negative : principalMeasure M (Iio 0) = 0 := by
  rw [principalMeasure, Measure.map_apply (spectralParameter_measurable M) measurableSet_Iio]
  have hs : spectralParameter M ⁻¹' Iio 0 =
      {t : spectrum ℝ (neumannResolvent M) | (t : ℝ) = 0} := by
    ext t
    change (t : ℝ)⁻¹ - 1 < 0 ↔ (t : ℝ) = 0
    obtain ⟨ht0, ht1⟩ := neumannResolvent_spectrum_bounds M t.property
    by_cases hz : (t : ℝ) = 0
    · simp [hz]
    · have hp : 0 < (t : ℝ) := lt_of_le_of_ne ht0 (Ne.symm hz)
      have hi : 1 ≤ (t : ℝ)⁻¹ := (one_le_inv₀ hp).2 ht1
      constructor
      · intro h
        linarith
      · exact fun h ↦ (hz h).elim
  rw [hs, resolventMeasure_zero]

/-- A proved finite cumulative mass limit yields the actual principal atom,
with finiteness inferred from that limit rather than separately postulated. -/
theorem principalMeasure_zero_of_cumulative_limit (M : Mass) {m : ℝ}
    (hm : Filter.Tendsto M.cumulative Filter.atTop (𝓝 m)) :
    letI := finiteMass_of_cumulative_limit M hm
    principalMeasure M {0} = ENNReal.ofReal m⁻¹ := by
  let _ := finiteMass_of_cumulative_limit M hm
  rw [principalMeasure_zero, real_totalMass_of_cumulative_limit M hm]

/-- The measure has the actual Neumann resolvent moments at the boundary.
Together with the weak energy equation this records the spectral
identification, independently of the reciprocal-atom computation. -/
theorem principalMeasure_resolvent_moment (k : ℕ) :
    (∫ ζ, ((1 + ζ)⁻¹ : ℝ) ^ k ∂principalMeasure M) =
      vectorFunctional (boundaryVector M) (((neumannResolvent M) ^ k) (boundaryVector M)) := by
  have hm : Measurable (fun ζ : ℝ ↦ ((1 + ζ)⁻¹ : ℝ) ^ k) := by fun_prop
  rw [principalMeasure, integral_map (spectralParameter_measurable M).aemeasurable
    hm.aestronglyMeasurable]
  have he : (fun t : spectrum ℝ (neumannResolvent M) ↦
      ((1 + spectralParameter M t)⁻¹ : ℝ) ^ k) =
        fun t : spectrum ℝ (neumannResolvent M) ↦ (t : ℝ) ^ k := by
    funext t
    unfold spectralParameter
    have hs : 1 + ((t : ℝ)⁻¹ - 1) = (t : ℝ)⁻¹ := by ring
    rw [hs, inv_inv]
  rw [he]
  exact scalarMeasure_moment _ _ _ _

theorem principalMeasure_resolvent_moment_integrable (k : ℕ) :
    Integrable (fun ζ : ℝ ↦ ((1 + ζ)⁻¹ : ℝ) ^ k) (principalMeasure M) := by
  have hm : Measurable (fun ζ : ℝ ↦ ((1 + ζ)⁻¹ : ℝ) ^ k) := by fun_prop
  change Integrable _ ((resolventMeasure M).map (spectralParameter M))
  apply (integrable_map_measure
    hm.aestronglyMeasurable
    (spectralParameter_measurable M).aemeasurable).2
  have : CompactSpace (spectrum ℝ (neumannResolvent M)) :=
    isCompact_iff_compactSpace.mp (spectrum.isCompact (neumannResolvent M))
  have hc : Continuous (fun t : spectrum ℝ (neumannResolvent M) ↦ (t : ℝ) ^ k) :=
    continuous_subtype_val.pow k
  have hi : Integrable (fun t : spectrum ℝ (neumannResolvent M) ↦ (t : ℝ) ^ k)
      (resolventMeasure M) := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      hc.continuousOn.integrableOn_compact (μ := resolventMeasure M) isCompact_univ
  convert hi using 1
  funext t
  simp only [Function.comp_def, spectralParameter]
  have hs : 1 + ((t : ℝ)⁻¹ - 1) = (t : ℝ)⁻¹ := by ring
  rw [hs, inv_inv]

end
end krylov.Strings.Spectral
