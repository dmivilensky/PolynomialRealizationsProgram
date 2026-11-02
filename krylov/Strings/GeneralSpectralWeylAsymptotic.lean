import krylov.Strings.GeneralSpectralWeylLimits
import krylov.Strings.GeneralSpectralWeylTrial
import krylov.Strings.TailTauberian

/-!
Article: main_krylov, apC:prop:tauber, the actual local Weyl law.
Use: squeeze the constructed physical boundary resolvent between genuine
local energy comparisons, then apply the proved Stieltjes Tauberian theorem.
Only initial mass-density comparisons enter; no spectral asymptotic or tail
conclusion is included in the input.
Source: the actual weak energy solution, compact exponential trial and
elementary sharp comparison limits.
-/

namespace krylov.Strings.GeneralSpectral
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- The actual real-positive physical Stieltjes defect, extended by zero
outside the positive parameter axis only to state ordinary real limits. -/
def physicalDefect (S : StringMeasure) (t : ℝ) : ℝ :=
  if ht : 0 < t then 1 - t * boundaryCompliance S t ht else 0

/-- Lower local density gives the sharp lower asymptotic comparison for
the true physical defect; no global mass or endpoint condition is used. -/
theorem lowerWeyl_eventually_le_defect (S : StringMeasure) {δ ρ : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hf : S.measure (Icc 0 δ) ≠ ⊤)
    (hlower : ENNReal.ofReal ρ • volume.restrict (Ioc 0 δ) ≤ S.measure.restrict (Ioc 0 δ)) :
    ∀ᶠ t : ℝ in atTop, Real.sqrt t * lowerWeylCoefficient δ ρ t /
      (t + lowerWeylCoefficient δ ρ t) ≤ Real.sqrt t * physicalDefect S t := by
  filter_upwards [eventually_gt_atTop (0 : ℝ), lowerWeylCoefficient_eventually_nonneg hρ] with t ht hk
  have hb := boundaryCompliance_le_local S hδ hρ ht hk hf hlower
    (lowerWeylCoefficient_energy_bound hδ hρ.le ht.le)
  have hd : 0 < t + lowerWeylCoefficient δ ρ t := add_pos_of_pos_of_nonneg ht hk
  have he : lowerWeylCoefficient δ ρ t / (t + lowerWeylCoefficient δ ρ t) =
      1 - t * (1 / (t + lowerWeylCoefficient δ ρ t)) := by field_simp; ring
  rw [mul_div_assoc, he, physicalDefect, dite_eq_left ht]
  exact mul_le_mul_of_nonneg_left (sub_le_sub_left (mul_le_mul_of_nonneg_left hb ht.le) 1)
    (Real.sqrt_nonneg _)

/-- The genuine compact exponential trial gives the sharp upper
asymptotic comparison for the actual physical Stieltjes defect. -/
theorem defect_eventually_le_upperWeyl (S : StringMeasure) {δ ρ : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hf : S.measure (Icc 0 δ) ≠ ⊤)
    (hphysical : S.measure (Iio 0) = 0)
    (hupper : S.measure.restrict (Ioc 0 δ) ≤ ENNReal.ofReal ρ • volume.restrict (Ioc 0 δ)) :
    ∀ᶠ t : ℝ in atTop, Real.sqrt t * physicalDefect S t ≤
      Real.sqrt t * upperWeylCoefficient δ ρ t / (t + upperWeylCoefficient δ ρ t) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  obtain ⟨w, hw, htrace, hE⟩ := exists_exponential_trial S hδ hρ ht hf hphysical hupper
  have hk : 0 < upperWeylCoefficient δ ρ t :=
    div_pos (Real.sqrt_pos.mpr (mul_pos ht hρ)) (sq_pos_of_pos (trialDenominator_pos hδ
      (Real.sqrt_pos.mpr (mul_pos ht hρ))))
  have hD : 0 < t + upperWeylCoefficient δ ρ t := add_pos ht hk
  have hb : 1 / (t + upperWeylCoefficient δ ρ t) ≤ boundaryCompliance S t ht :=
    le_boundaryCompliance_of_trial S t ht hD hw htrace hE
  have he : upperWeylCoefficient δ ρ t / (t + upperWeylCoefficient δ ρ t) =
      1 - t * (1 / (t + upperWeylCoefficient δ ρ t)) := by field_simp; ring
  rw [mul_div_assoc, he, physicalDefect, dite_eq_left ht]
  exact mul_le_mul_of_nonneg_left (sub_le_sub_left (mul_le_mul_of_nonneg_left hb ht.le) 1)
    (Real.sqrt_nonneg _)

/-- The actual physical Weyl half-power law follows from arbitrarily
close positive lower and upper initial density comparisons.  These are
local properties of the mass measure and make no spectral assertion. -/
theorem physicalDefect_sqrt_tendsto (S : StringMeasure) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hphysical : S.measure (Iio 0) = 0)
    (hlower : ∀ ρ, 0 < ρ → ρ < ρ₀ → ∃ δ, 0 < δ ∧ S.measure (Icc 0 δ) ≠ ⊤ ∧
      ENNReal.ofReal ρ • volume.restrict (Ioc 0 δ) ≤ S.measure.restrict (Ioc 0 δ))
    (hupper : ∀ ρ, ρ₀ < ρ → ∃ δ, 0 < δ ∧ S.measure (Icc 0 δ) ≠ ⊤ ∧
      S.measure.restrict (Ioc 0 δ) ≤ ENNReal.ofReal ρ • volume.restrict (Ioc 0 δ)) :
    Tendsto (fun t : ℝ ↦ Real.sqrt t * physicalDefect S t) atTop (𝓝 (Real.sqrt ρ₀)) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    obtain ⟨a, ha0, hba, ha⟩ : ∃ a, 0 < a ∧ b < a ∧ a < Real.sqrt ρ₀ := by
      obtain ⟨a, ha, ha'⟩ := exists_between (max_lt (Real.sqrt_pos.mpr hρ₀) hb)
      exact ⟨a, (lt_of_le_of_lt (le_max_left _ _) ha),
        lt_of_le_of_lt (le_max_right _ _) ha, ha'⟩
    have har : a ^ 2 < ρ₀ := by nlinarith [Real.sq_sqrt hρ₀.le]
    obtain ⟨δ, hδ, hf, hμ⟩ := hlower (a ^ 2) (sq_pos_of_pos ha0) har
    have hlim := lowerWeyl_defect_tendsto (δ := δ) (ρ := a ^ 2)
    rw [Real.sqrt_sq ha0.le] at hlim
    have hh := hlim.eventually (lt_mem_nhds hba)
    filter_upwards [hh, lowerWeyl_eventually_le_defect S hδ (sq_pos_of_pos ha0) hf hμ]
      with t ht hbound
    exact ht.trans_le hbound
  · intro b hb
    obtain ⟨a, ha, hab⟩ := exists_between hb
    have ha0 : 0 < a := (Real.sqrt_pos.mpr hρ₀).trans ha
    have har : ρ₀ < a ^ 2 := by
      have hh := (sq_lt_sq₀ (Real.sqrt_nonneg ρ₀) ha0.le).mpr ha
      rwa [Real.sq_sqrt hρ₀.le] at hh
    obtain ⟨δ, hδ, hf, hμ⟩ := hupper (a ^ 2) har
    have hlim := upperWeyl_defect_tendsto hδ (sq_pos_of_pos ha0)
    rw [Real.sqrt_sq ha0.le] at hlim
    have hh := hlim.eventually (gt_mem_nhds hab)
    filter_upwards [hh, defect_eventually_le_upperWeyl S hδ (sq_pos_of_pos ha0) hf hphysical hμ]
      with t ht hbound
    exact hbound.trans_lt ht

/-- The constructed actual principal probability measure obeys the
positive-real Stieltjes half-power law from initial density comparisons. -/
theorem principalMeasure_sqrt_defect_tendsto (S : StringMeasure) (N : ℕ)
    (hN : S.measure (Icc 0 (Spectral.tentScale N)) ≠ ⊤) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hphysical : S.measure (Iio 0) = 0)
    (hlower : ∀ ρ, 0 < ρ → ρ < ρ₀ → ∃ δ, 0 < δ ∧ S.measure (Icc 0 δ) ≠ ⊤ ∧
      ENNReal.ofReal ρ • volume.restrict (Ioc 0 δ) ≤ S.measure.restrict (Ioc 0 δ))
    (hupper : ∀ ρ, ρ₀ < ρ → ∃ δ, 0 < δ ∧ S.measure (Icc 0 δ) ≠ ⊤ ∧
      S.measure.restrict (Ioc 0 δ) ≤ ENNReal.ofReal ρ • volume.restrict (Ioc 0 δ)) :
    Tendsto (fun t : ℝ ↦ Real.sqrt t * ∫ ξ, ξ / (ξ + t) ∂principalMeasure S)
      atTop (𝓝 (Real.sqrt ρ₀)) := by
  apply (physicalDefect_sqrt_tendsto S hρ₀ hphysical hlower hupper).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [physicalDefect, dite_eq_left ht, principalMeasure_defect S N hN hphysical t ht]

/-- Both sharp source spectral tails hold for the actual constructed
principal measure, with coefficient 2*sqrt(rho0)/pi. -/
theorem principalMeasure_half_tails (S : StringMeasure) (N : ℕ)
    (hN : S.measure (Icc 0 (Spectral.tentScale N)) ≠ ⊤) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hphysical : S.measure (Iio 0) = 0)
    (hlower : ∀ ρ, 0 < ρ → ρ < ρ₀ → ∃ δ, 0 < δ ∧ S.measure (Icc 0 δ) ≠ ⊤ ∧
      ENNReal.ofReal ρ • volume.restrict (Ioc 0 δ) ≤ S.measure.restrict (Ioc 0 δ))
    (hupper : ∀ ρ, ρ₀ < ρ → ∃ δ, 0 < δ ∧ S.measure (Icc 0 δ) ≠ ⊤ ∧
      S.measure.restrict (Ioc 0 δ) ≤ ENNReal.ofReal ρ • volume.restrict (Ioc 0 δ)) :
    Tendsto (fun x : ℝ ↦ (∫ ξ in Ioc 0 x, ξ ∂principalMeasure S) / Real.sqrt x)
      atTop (𝓝 (2 * Real.sqrt ρ₀ / Real.pi)) ∧
    Tendsto (fun x : ℝ ↦ Real.sqrt x * (principalMeasure S).real (Ioi x))
      atTop (𝓝 (2 * Real.sqrt ρ₀ / Real.pi)) :=
  Tail.stieltjes_half_tauberian (principalMeasure S) (principalMeasure_negative S N hN hphysical)
    (Real.sqrt_nonneg _) (principalMeasure_sqrt_defect_tendsto S N hN hρ₀ hphysical hlower hupper)

end
end krylov.Strings.GeneralSpectral
