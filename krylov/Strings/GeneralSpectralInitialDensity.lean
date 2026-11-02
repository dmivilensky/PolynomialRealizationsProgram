import krylov.Strings.GeneralSpectralWeylAsymptotic

/-!
Article: main_krylov, apC:prop:tauber, the essential initial-density input.
Use: derive the genuine local mass comparisons from an actual absolutely
continuous initial mass interval and the source's essential positive density
limit.  Pointwise continuity is not required for the general result.
Source: the epsilon-delta definition of an essential right limit and
monotonicity of actual measures with density.
-/

namespace krylov.Strings.GeneralSpectral
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- An essential right limit at the origin, in its ordinary epsilon-delta
form. Exceptional density values on Lebesgue-null sets are unrestricted. -/
def HasEssentialRightLimit (ρ : ℝ → ℝ) (r : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ, 0 < δ ∧ ∀ᵐ x ∂volume.restrict (Ioc 0 δ), |ρ x - r| < ε

/-- Ordinary continuity at the origin implies the essential right limit
used for general strings; this specializes the source input to optimizers. -/
theorem hasEssentialRightLimit_of_continuousAt {ρ : ℝ → ℝ} (hc : ContinuousAt ρ 0) :
    HasEssentialRightLimit ρ (ρ 0) := by
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := Metric.continuousAt_iff.mp hc ε hε
  refine ⟨δ / 2, by positivity, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have hd : dist x 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hx.1]
    linarith [hx.2]
  simpa only [Real.dist_eq] using hbound hd

/-- Essential convergence gives simultaneous density bounds on an
arbitrarily small positive initial interval. -/
theorem HasEssentialRightLimit.exists_bounds {ρ : ℝ → ℝ} {r a b δ₀ : ℝ}
    (hlim : HasEssentialRightLimit ρ r) (ha : a < r) (hb : r < b) (hδ₀ : 0 < δ₀) :
    ∃ δ, 0 < δ ∧ δ ≤ δ₀ ∧ ∀ᵐ x ∂volume.restrict (Ioc 0 δ), a ≤ ρ x ∧ ρ x ≤ b := by
  let ε := min (r - a) (b - r) / 2
  have hε : 0 < ε := by dsimp only [ε]; positivity
  obtain ⟨δ', hδ', hbound⟩ := hlim ε hε
  let δ := min δ' δ₀
  have hδ : 0 < δ := lt_min hδ' hδ₀
  refine ⟨δ, hδ, min_le_right _ _, ?_⟩
  have hsub : Ioc (0 : ℝ) δ ⊆ Ioc 0 δ' := Ioc_subset_Ioc_right (min_le_left _ _)
  have hh : ∀ᵐ x ∂volume.restrict (Ioc 0 δ), |ρ x - r| < ε :=
    hbound.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  filter_upwards [hh] with x hx
  have he1 : ε ≤ (r - a) / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have he2 : ε ≤ (b - r) / 2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  constructor <;> linarith [neg_abs_le (ρ x - r), le_abs_self (ρ x - r)]

/-- An actual initial mass-density identity restricts exactly to every
smaller physical prefix. -/
theorem initial_density_restrict (S : StringMeasure) {ρ : ℝ → ℝ} {δ δ₀ : ℝ}
    (hδ : δ ≤ δ₀)
    (hdensity : S.measure.restrict (Ioc 0 δ₀) =
      (volume.restrict (Ioc 0 δ₀)).withDensity (fun x ↦ ENNReal.ofReal (ρ x))) :
    S.measure.restrict (Ioc 0 δ) =
      (volume.restrict (Ioc 0 δ)).withDensity (fun x ↦ ENNReal.ofReal (ρ x)) := by
  have hh := congrArg (fun μ : Measure ℝ ↦ μ.restrict (Ioc 0 δ)) hdensity
  have hsub : Ioc (0 : ℝ) δ ⊆ Ioc 0 δ₀ := Ioc_subset_Ioc_right hδ
  simpa only [restrict_withDensity measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.mpr hsub] using hh

/-- Actual local absolute continuity and an essential initial density
limit produce the two genuine mass comparisons required by the Weyl proof. -/
theorem initial_density_comparisons (S : StringMeasure) {ρ : ℝ → ℝ} {r a b δ₀ : ℝ}
    (hδ₀ : 0 < δ₀) (hf₀ : S.measure (Icc 0 δ₀) ≠ ⊤)
    (hdensity : S.measure.restrict (Ioc 0 δ₀) =
      (volume.restrict (Ioc 0 δ₀)).withDensity (fun x ↦ ENNReal.ofReal (ρ x)))
    (hlim : HasEssentialRightLimit ρ r) (ha : a < r) (hb : r < b) :
    ∃ δ, 0 < δ ∧ S.measure (Icc 0 δ) ≠ ⊤ ∧
      ENNReal.ofReal a • volume.restrict (Ioc 0 δ) ≤ S.measure.restrict (Ioc 0 δ) ∧
      S.measure.restrict (Ioc 0 δ) ≤ ENNReal.ofReal b • volume.restrict (Ioc 0 δ) := by
  obtain ⟨δ, hδ, hδ', hbound⟩ := hlim.exists_bounds ha hb hδ₀
  have hf : S.measure (Icc 0 δ) ≠ ⊤ :=
    ne_top_of_le_ne_top hf₀ (measure_mono (Icc_subset_Icc_right hδ'))
  refine ⟨δ, hδ, hf, ?_, ?_⟩
  · rw [initial_density_restrict S hδ' hdensity, ← withDensity_const]
    exact withDensity_mono (hbound.mono fun x hx ↦ ENNReal.ofReal_le_ofReal hx.1)
  · rw [initial_density_restrict S hδ' hdensity, ← withDensity_const]
    exact withDensity_mono (hbound.mono fun x hx ↦ ENNReal.ofReal_le_ofReal hx.2)

/-- General physical Weyl law under precisely local absolute continuity
and an essential positive initial density limit.  No total-mass bound or
pointwise density regularity is imposed. -/
theorem physicalDefect_sqrt_tendsto_of_initial_density (S : StringMeasure)
    {ρ : ℝ → ℝ} {r δ₀ : ℝ} (hr : 0 < r) (hδ₀ : 0 < δ₀)
    (hf₀ : S.measure (Icc 0 δ₀) ≠ ⊤) (hphysical : S.measure (Iio 0) = 0)
    (hdensity : S.measure.restrict (Ioc 0 δ₀) =
      (volume.restrict (Ioc 0 δ₀)).withDensity (fun x ↦ ENNReal.ofReal (ρ x)))
    (hlim : HasEssentialRightLimit ρ r) :
    Tendsto (fun t : ℝ ↦ Real.sqrt t * physicalDefect S t) atTop (𝓝 (Real.sqrt r)) := by
  apply physicalDefect_sqrt_tendsto S hr hphysical
  · intro a _ ha
    obtain ⟨δ, hδ, hf, hl, _⟩ := initial_density_comparisons S hδ₀ hf₀ hdensity hlim ha
      (by linarith : r < r + 1)
    exact ⟨δ, hδ, hf, hl⟩
  · intro b hb
    obtain ⟨δ, hδ, hf, _, hu⟩ := initial_density_comparisons S hδ₀ hf₀ hdensity hlim
      (by linarith : r / 2 < r) hb
    exact ⟨δ, hδ, hf, hu⟩

end
end krylov.Strings.GeneralSpectral
