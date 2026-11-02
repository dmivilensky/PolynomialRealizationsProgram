import krylov.Strings.GeneralSpectralInitialDensity
import krylov.Strings.GeneralSpectralFinite
import krylov.Strings.SpectralHalf

/-!
Article: main_krylov, apC:prop:tauber and thm:tail.
Use: the exact general spectral-tail theorem for the actual physical
principal measure, and its specialization to the same unique half-gamma
optimizer whose zero atom and qualitative regularity were already proved.
Source: actual local energy Weyl comparison and the proved index-one-half
Stieltjes Tauberian theorem.  The separate identification with a spectral
function defined by generalized-eigenfunction isometry is not assumed here.
-/

/-!
Article: krylov, Proposition D.22 [apC:prop:tauber].

For the genuine canonical principal energy measure, a positive essential initial density limit
gives both exact weighted-moment and tail equivalents.
Only local absolute continuity near the origin is required; finite/infinite physical lengths
and arbitrary global mass are represented, with the principal endpoint convention fixed.
-/

namespace krylov.Strings.GeneralSpectral
noncomputable section
open Set Filter MeasureTheory Asymptotics
open scoped Topology ENNReal NNReal

/-- A finite positive initial prefix contains a finite-prefix tent. -/
theorem exists_finite_tent_prefix (S : StringMeasure) {δ : ℝ} (hδ : 0 < δ)
    (hf : S.measure (Icc 0 δ) ≠ ⊤) :
    ∃ N : ℕ, S.measure (Icc 0 (Spectral.tentScale N)) ≠ ⊤ := by
  obtain ⟨N, hN⟩ := (Spectral.tentScale_tendsto.eventually (gt_mem_nhds hδ)).exists
  exact ⟨N, ne_top_of_le_ne_top hf (measure_mono (Icc_subset_Icc_right hN.le))⟩

/-- The general actual principal measure has the source real-positive
Stieltjes asymptotic from only essential positive initial density. -/
theorem principalMeasure_sqrt_defect_of_initial_density (S : StringMeasure)
    {ρ : ℝ → ℝ} {r δ₀ : ℝ} (hr : 0 < r) (hδ₀ : 0 < δ₀)
    (hf₀ : S.measure (Icc 0 δ₀) ≠ ⊤) (hphysical : S.measure (Iio 0) = 0)
    (hdensity : S.measure.restrict (Ioc 0 δ₀) =
      (volume.restrict (Ioc 0 δ₀)).withDensity (fun x ↦ ENNReal.ofReal (ρ x)))
    (hlim : HasEssentialRightLimit ρ r) :
    Tendsto (fun t : ℝ ↦ Real.sqrt t * ∫ ξ, ξ / (ξ + t) ∂principalMeasure S)
      atTop (𝓝 (Real.sqrt r)) := by
  obtain ⟨N, hN⟩ := exists_finite_tent_prefix S hδ₀ hf₀
  apply (physicalDefect_sqrt_tendsto_of_initial_density S hr hδ₀ hf₀ hphysical hdensity hlim).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [physicalDefect, dite_eq_left ht, principalMeasure_defect S N hN hphysical t ht]

/-- Both sharp source tail limits for the constructed physical principal
measure of an arbitrary string, with essential initial density r>0.
Infinite total mass and singular finite endpoints are permitted. -/
theorem principalMeasure_tails_of_initial_density (S : StringMeasure)
    {ρ : ℝ → ℝ} {r δ₀ : ℝ} (hr : 0 < r) (hδ₀ : 0 < δ₀)
    (hf₀ : S.measure (Icc 0 δ₀) ≠ ⊤) (hphysical : S.measure (Iio 0) = 0)
    (hdensity : S.measure.restrict (Ioc 0 δ₀) =
      (volume.restrict (Ioc 0 δ₀)).withDensity (fun x ↦ ENNReal.ofReal (ρ x)))
    (hlim : HasEssentialRightLimit ρ r) :
    Tendsto (fun x : ℝ ↦ (∫ ξ in Ioc 0 x, ξ ∂principalMeasure S) / Real.sqrt x)
      atTop (𝓝 (2 * Real.sqrt r / Real.pi)) ∧
    Tendsto (fun x : ℝ ↦ Real.sqrt x * (principalMeasure S).real (Ioi x))
      atTop (𝓝 (2 * Real.sqrt r / Real.pi)) := by
  obtain ⟨N, hN⟩ := exists_finite_tent_prefix S hδ₀ hf₀
  exact Tail.stieltjes_half_tauberian (principalMeasure S) (principalMeasure_negative S N hN hphysical)
    (Real.sqrt_nonneg _) (principalMeasure_sqrt_defect_of_initial_density S hr hδ₀ hf₀ hphysical hdensity hlim)

/-- The same general physical tail theorem in the asymptotic-equivalence
notation printed in the source proposition. -/
theorem principalMeasure_tail_asymptotics_of_initial_density (S : StringMeasure)
    {ρ : ℝ → ℝ} {r δ₀ : ℝ} (hr : 0 < r) (hδ₀ : 0 < δ₀)
    (hf₀ : S.measure (Icc 0 δ₀) ≠ ⊤) (hphysical : S.measure (Iio 0) = 0)
    (hdensity : S.measure.restrict (Ioc 0 δ₀) =
      (volume.restrict (Ioc 0 δ₀)).withDensity (fun x ↦ ENNReal.ofReal (ρ x)))
    (hlim : HasEssentialRightLimit ρ r) :
    (fun x : ℝ ↦ ∫ ξ in Ioc 0 x, ξ ∂principalMeasure S) ~[atTop]
      (fun x : ℝ ↦ (2 * Real.sqrt r / Real.pi) * Real.sqrt x) ∧
    (fun x : ℝ ↦ (principalMeasure S).real (Ioi x)) ~[atTop]
      (fun x : ℝ ↦ (2 * Real.sqrt r / Real.pi) / Real.sqrt x) := by
  obtain ⟨N, hN⟩ := exists_finite_tent_prefix S hδ₀ hf₀
  exact Tail.stieltjes_half_asymptotics (principalMeasure S) (principalMeasure_negative S N hN hphysical)
    (Real.sqrt_pos.mpr hr) (principalMeasure_sqrt_defect_of_initial_density S hr hδ₀ hf₀ hphysical hdensity hlim)

/-- The density attached to the actual optimizer represents its literal
local physical mass, not merely an almost-everywhere RN function. -/
theorem regularOptimizerDensity_measure (M : Mass) {v : ℝ → ℝ} {s₀ : ℝ}
    (h : RegularOptimizerDensity M v s₀) (L : ℝ≥0) :
    M.measure.restrict (Ioc 0 (L : ℝ)) =
      (volume.restrict (Ioc 0 (L : ℝ))).withDensity (fun x ↦ ENNReal.ofReal (v x ^ 2)) := by
  have he : M.measure.restrict (Ioc 0 (L : ℝ)) =
      (OptimizerDensity.globalMass v h.continuous).measure.restrict (Ioc 0 (L : ℝ)) := by
    apply LocalMass.measure_restrict_eq_of_cumulative_eq
    intro x hx
    rw [h.cumulative x hx.1, OptimizerDensity.globalCumulative_eq v h.continuous hx.1]
  exact he.trans (OptimizerDensity.globalMass_restrict_density v h.continuous L) |>.trans
    (restrict_withDensity measurableSet_Ioc _)

/-- All regular physical optimizer densities yield the sharp tail on
their same actual principal measure; this does not construct a second mass. -/
theorem regularOptimizerDensity_principal_tails (M : Mass) [IsFiniteMeasure M.measure]
    {v : ℝ → ℝ} {s₀ : ℝ} (h : RegularOptimizerDensity M v s₀) :
    Tendsto (fun x : ℝ ↦ (∫ ξ in Ioc 0 x, ξ ∂Spectral.principalMeasure M) / Real.sqrt x)
      atTop (𝓝 (2 / (Real.pi * Real.sqrt s₀))) ∧
    Tendsto (fun x : ℝ ↦ Real.sqrt x * (Spectral.principalMeasure M).real (Ioi x))
      atTop (𝓝 (2 / (Real.pi * Real.sqrt s₀))) := by
  have hv : 0 < v 0 := h.positive 0 le_rfl
  have : IsFiniteMeasure (StringMeasure.ofMass M).measure :=
    inferInstanceAs (IsFiniteMeasure M.measure)
  have hphysical : (StringMeasure.ofMass M).measure (Iio 0) = 0 := by
    change M.measure (Iio 0) = 0
    simpa only [ae_iff, not_le, Iio] using Spectral.mass_ae_nonnegative M
  have hh := principalMeasure_tails_of_initial_density (StringMeasure.ofMass M)
    (r := v 0 ^ 2) (δ₀ := 1) (sq_pos_of_pos hv) (by norm_num)
    (measure_ne_top _ _) hphysical
    (regularOptimizerDensity_measure M h 1)
    (hasEssentialRightLimit_of_continuousAt ((h.continuous.pow 2).continuousAt))
  rw [principalMeasure_ofMass, Real.sqrt_sq hv.le, h.initial_density] at hh
  have hc : 2 * (1 / Real.sqrt s₀) / Real.pi = 2 / (Real.pi * Real.sqrt s₀) := by ring
  rwa [hc] at hh

end
end krylov.Strings.GeneralSpectral

namespace krylov.Strings.Spectral
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

/-- The very same unique half-gamma optimizer has its proved probability
principal measure, reciprocal origin atom and both sharp spectral tails.
The coefficient is 2/(pi*a), where a=sqrt(sigma(1)) is the attained value. -/
theorem actualRegularMaximum_half_principal_tails {σ : ℝ → ℝ} {M : Mass} {φ v : ℝ → ℝ}
    (h : ActualRegularMaximum (1 / 2) σ M φ v) :
    ∃ hfinite : IsFiniteMeasure M.measure,
      IsProbabilityMeasure (@principalMeasure M hfinite) ∧
      @principalMeasure M hfinite (Iio 0) = 0 ∧
      @principalMeasure M hfinite {0} = ENNReal.ofReal (σ 1)⁻¹ ∧
      Tendsto (fun x : ℝ ↦ (∫ ξ in Ioc 0 x, ξ ∂@principalMeasure M hfinite) / Real.sqrt x)
        atTop (𝓝 (2 / (Real.pi * Real.sqrt (σ 1)))) ∧
      Tendsto (fun x : ℝ ↦ Real.sqrt x * (@principalMeasure M hfinite).real (Ioi x))
        atTop (𝓝 (2 / (Real.pi * Real.sqrt (σ 1)))) := by
  obtain ⟨hf, hp, hn, hz⟩ := actualRegularMaximum_half_principal h
  let : IsFiniteMeasure M.measure := hf
  exact ⟨hf, hp, hn, hz, GeneralSpectral.regularOptimizerDensity_principal_tails M h.density⟩

/-- Unconditional existence of one actual unique half-gamma maximizing
string with its actual principal probability measure, exact zero atom and
both sharp spectral tails.  All qualitative conclusions concern this mass. -/
theorem exists_actual_half_principal_tail_attainment :
    ∃ σ : ℝ → ℝ,
      (∀ r ≥ 1, AnalyticAt ℝ σ r ∧ krylov.ContinuumControl.FeedbackGraphAt (1 / 2) σ r) ∧
      ∃ M : Mass, ∃ φ v : ℝ → ℝ,
      ActualRegularMaximum (1 / 2) σ M φ v ∧
      ∃ hfinite : IsFiniteMeasure M.measure,
      IsProbabilityMeasure (@principalMeasure M hfinite) ∧
      @principalMeasure M hfinite (Iio 0) = 0 ∧
      @principalMeasure M hfinite {0} = ENNReal.ofReal (σ 1)⁻¹ ∧
      Tendsto (fun x : ℝ ↦ (∫ ξ in Ioc 0 x, ξ ∂@principalMeasure M hfinite) / Real.sqrt x)
        atTop (𝓝 (2 / (Real.pi * Real.sqrt (σ 1)))) ∧
      Tendsto (fun x : ℝ ↦ Real.sqrt x * (@principalMeasure M hfinite).real (Ioi x))
        atTop (𝓝 (2 / (Real.pi * Real.sqrt (σ 1)))) := by
  obtain ⟨σ, hσ, M, φ, v, h⟩ := exists_actual_regular_maximum
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
  exact ⟨σ, hσ, M, φ, v, h, actualRegularMaximum_half_principal_tails h⟩

end
end krylov.Strings.Spectral
