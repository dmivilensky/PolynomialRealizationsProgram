import krylov.Strings.GeneralSpectralSourceMeasure
import krylov.Strings.GeneralSpectralTail

/-!
Article: main_krylov, apC:prop:tauber, actual finite-length source strings.
Use: obtain the physical principal-measure tail directly from the printed
local cumulative-mass hypothesis on `[0,ℓ)`, even when mass diverges at ℓ.
The corrected source uses the explicit canonical principal energy measure;
no identification with a bare generalized-eigenfunction isometry is assumed.
Source: uniqueness of Stieltjes mass increments, the Lebesgue integral and
the proved actual physical Weyl and Stieltjes Tauberian theorems.
-/

namespace krylov.Strings.GeneralSpectral
noncomputable section
open Set Filter MeasureTheory Asymptotics
open scoped Topology NNReal

/-- The literal source formula `M(x)=1+∫₀ˣρ` identifies the actual local
post-origin mass measure, including merely measurable density. -/
theorem finiteSourceMeasure_density {ℓ δ : ℝ} (hℓ : 0 < ℓ)
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ)) (hδ : 0 ≤ δ) (hδℓ : δ < ℓ)
    {ρ : ℝ → ℝ} (hi : IntervalIntegrable ρ volume 0 δ)
    (hn : ∀ᵐ x ∂volume.restrict (Ioc 0 δ), 0 ≤ ρ x)
    (hcumulative : ∀ x (hx : x ∈ Icc 0 δ),
      f ⟨x, ⟨hx.1, hx.2.trans_lt hδℓ⟩⟩ = 1 + ∫ t in (0 : ℝ)..x, ρ t) :
    (finiteSourceMeasure f).restrict (Ioc 0 δ) =
      (volume.restrict (Ioc 0 δ)).withDensity (fun x ↦ ENNReal.ofReal (ρ x)) := by
  rw [← restrict_withDensity measurableSet_Ioc]
  have : IsFiniteMeasure ((finiteSourceMeasure f).restrict (Ioc 0 δ)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact (measure_mono Ioc_subset_Icc_self).trans_lt (lt_top_iff_ne_top.mpr
      (finiteSourceMeasure_prefix_finite hℓ f ⟨δ, hδ⟩ hδℓ))
  apply Measure.ext_of_Ioc
  intro a b _hab
  rw [Measure.restrict_apply measurableSet_Ioc, Measure.restrict_apply measurableSet_Ioc,
    Ioc_inter_Ioc]
  by_cases hne : max a 0 < min b δ
  · have hlo : max a 0 ∈ Icc 0 δ :=
      ⟨le_max_right _ _, hne.le.trans (min_le_right _ _)⟩
    have hhi : min b δ ∈ Icc 0 δ :=
      ⟨(le_max_right _ _).trans hne.le, min_le_right _ _⟩
    have hsub : Ioc (max a 0) (min b δ) ⊆ Ioc 0 δ :=
      Ioc_subset_Ioc (le_max_right _ _) (min_le_right _ _)
    have hilo : IntervalIntegrable ρ volume 0 (max a 0) := by
      apply hi.mono_set
      rw [uIcc_of_le hlo.1, uIcc_of_le hδ]
      exact Icc_subset_Icc_right hlo.2
    have hihi : IntervalIntegrable ρ volume 0 (min b δ) := by
      apply hi.mono_set
      rw [uIcc_of_le hhi.1, uIcc_of_le hδ]
      exact Icc_subset_Icc_right hhi.2
    rw [finiteSourceMeasure_Ioc f ⟨hlo.1, hlo.2.trans_lt hδℓ⟩
      ⟨hhi.1, hhi.2.trans_lt hδℓ⟩,
      hcumulative _ hhi, hcumulative _ hlo]
    have he : (1 + ∫ t in (0 : ℝ)..min b δ, ρ t) -
        (1 + ∫ t in (0 : ℝ)..max a 0, ρ t) =
          ∫ t in max a 0..min b δ, ρ t := by
      simpa only [add_sub_add_left_eq_sub] using
        intervalIntegral.integral_interval_sub_left hihi hilo
    rw [he, withDensity_apply _ measurableSet_Ioc, intervalIntegral.integral_of_le hne.le]
    exact ofReal_integral_eq_lintegral_ofReal
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hδ).1 hi |>.mono_set hsub)
      (hn.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)))
  · simp only [Ioc_eq_empty hne, measure_empty]

/-- Both exact tail limits for the actual physical principal measure of
a source finite-length string. Infinite endpoint mass is unrestricted;
the density and its essential limit are the source's local assumptions. -/
theorem finiteSource_principalMeasure_tails {ℓ δ r : ℝ} (hℓ : 0 < ℓ)
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ)) (hδ : 0 < δ) (hδℓ : δ < ℓ)
    {ρ : ℝ → ℝ} (hr : 0 < r) (hi : IntervalIntegrable ρ volume 0 δ)
    (hn : ∀ᵐ x ∂volume.restrict (Ioc 0 δ), 0 ≤ ρ x)
    (hcumulative : ∀ x (hx : x ∈ Icc 0 δ),
      f ⟨x, ⟨hx.1, hx.2.trans_lt hδℓ⟩⟩ = 1 + ∫ t in (0 : ℝ)..x, ρ t)
    (hlim : HasEssentialRightLimit ρ r) :
    Tendsto (fun x : ℝ ↦ (∫ ξ in Ioc 0 x, ξ ∂principalMeasure
      (StringMeasure.ofFiniteSource hℓ f)) / Real.sqrt x)
      atTop (𝓝 (2 * Real.sqrt r / Real.pi)) ∧
    Tendsto (fun x : ℝ ↦ Real.sqrt x * (principalMeasure
      (StringMeasure.ofFiniteSource hℓ f)).real (Ioi x))
      atTop (𝓝 (2 * Real.sqrt r / Real.pi)) := by
  exact principalMeasure_tails_of_initial_density (StringMeasure.ofFiniteSource hℓ f)
    hr hδ (finiteSourceMeasure_prefix_finite hℓ f ⟨δ, hδ.le⟩ hδℓ)
    (finiteSourceMeasure_negative f)
    (finiteSourceMeasure_density hℓ f hδ.le hδℓ hi hn hcumulative) hlim

/-- The source finite-endpoint conclusions in their printed asymptotic
equivalence form, for the constructed physical principal measure. -/
theorem finiteSource_principalMeasure_tail_asymptotics {ℓ δ r : ℝ} (hℓ : 0 < ℓ)
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ)) (hδ : 0 < δ) (hδℓ : δ < ℓ)
    {ρ : ℝ → ℝ} (hr : 0 < r) (hi : IntervalIntegrable ρ volume 0 δ)
    (hn : ∀ᵐ x ∂volume.restrict (Ioc 0 δ), 0 ≤ ρ x)
    (hcumulative : ∀ x (hx : x ∈ Icc 0 δ),
      f ⟨x, ⟨hx.1, hx.2.trans_lt hδℓ⟩⟩ = 1 + ∫ t in (0 : ℝ)..x, ρ t)
    (hlim : HasEssentialRightLimit ρ r) :
    (fun x : ℝ ↦ ∫ ξ in Ioc 0 x, ξ ∂principalMeasure
      (StringMeasure.ofFiniteSource hℓ f)) ~[atTop]
      (fun x : ℝ ↦ (2 * Real.sqrt r / Real.pi) * Real.sqrt x) ∧
    (fun x : ℝ ↦ (principalMeasure
      (StringMeasure.ofFiniteSource hℓ f)).real (Ioi x)) ~[atTop]
      (fun x : ℝ ↦ (2 * Real.sqrt r / Real.pi) / Real.sqrt x) := by
  exact principalMeasure_tail_asymptotics_of_initial_density
    (StringMeasure.ofFiniteSource hℓ f) hr hδ
    (finiteSourceMeasure_prefix_finite hℓ f ⟨δ, hδ.le⟩ hδℓ)
    (finiteSourceMeasure_negative f)
    (finiteSourceMeasure_density hℓ f hδ.le hδℓ hi hn hcumulative) hlim

end
end krylov.Strings.GeneralSpectral
