import krylov.Strings.GeneralSpectralWeylVariational
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
Article: main_krylov, apC:prop:tauber, sharp Weyl comparison limits.
Use: isolate the elementary square-root and exponential limits from the
physical variational argument.  The lower comparison uses k=sqrt(t*rho)-1/delta;
the upper comparison is the exact compact exponential-trial coefficient.
Source: algebra, the continuity of sqrt, and exp tending to zero at minus infinity.
-/

namespace krylov.Strings.GeneralSpectral
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

/-- The local lower trace coefficient, sharp to leading square-root order. -/
def lowerWeylCoefficient (δ ρ t : ℝ) : ℝ := Real.sqrt (t * ρ) - 1 / δ

/-- The actual compact-exponential trial coefficient. -/
def upperWeylCoefficient (δ ρ t : ℝ) : ℝ :=
  Real.sqrt (t * ρ) / (1 - Real.exp (-Real.sqrt (t * ρ) * δ)) ^ 2

/-- A coefficient with the correct square-root scale gives the desired
Stieltjes-defect scale after the unit origin atom is included. -/
theorem weyl_quotient_tendsto {q : ℝ → ℝ} {r : ℝ}
    (hq : Tendsto (fun t ↦ q t / Real.sqrt t) atTop (𝓝 r)) :
    Tendsto (fun t ↦ Real.sqrt t * q t / (t + q t)) atTop (𝓝 r) := by
  have hz := hq.div_atTop Real.tendsto_sqrt_atTop
  have hh := hq.div (tendsto_const_nhds.add hz) (by norm_num : (1 : ℝ) + 0 ≠ 0)
  simp only [add_zero, div_one] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hs := Real.sq_sqrt ht.le
  have hn := (Real.sqrt_pos.mpr ht).ne'
  change q t / Real.sqrt t / (1 + q t / Real.sqrt t / Real.sqrt t) = _
  have hd : 1 + q t / Real.sqrt t / Real.sqrt t = (t + q t) / t := by
    rw [div_div, ← pow_two, hs]
    field_simp
  rw [hd, div_div_eq_mul_div]
  congr 1
  field_simp [hn]
  rw [hs]

/-- The lower trace coefficient has the exact limiting square-root scale. -/
theorem lowerWeylCoefficient_scaled_tendsto {δ ρ : ℝ} :
    Tendsto (fun t ↦ lowerWeylCoefficient δ ρ t / Real.sqrt t) atTop
      (𝓝 (Real.sqrt ρ)) := by
  have hz : Tendsto (fun t : ℝ ↦ (1 / δ) / Real.sqrt t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have hh := (tendsto_const_nhds (x := Real.sqrt ρ)).sub hz
  simp only [sub_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [lowerWeylCoefficient, Real.sqrt_mul ht.le]
  field_simp [(Real.sqrt_pos.mpr ht).ne']

/-- The compact exponential-trial correction tends to one, so its energy
coefficient has the same exact leading square-root scale. -/
theorem upperWeylCoefficient_scaled_tendsto {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) :
    Tendsto (fun t ↦ upperWeylCoefficient δ ρ t / Real.sqrt t) atTop
      (𝓝 (Real.sqrt ρ)) := by
  have hk : Tendsto (fun t : ℝ ↦ Real.sqrt (t * ρ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp ((tendsto_mul_const_atTop_of_pos hρ).mpr tendsto_id)
  have hneg : Tendsto (fun t : ℝ ↦ -Real.sqrt (t * ρ) * δ) atTop atBot := by
    simpa only [Function.comp_def, neg_mul] using
      tendsto_neg_atTop_atBot.comp ((tendsto_mul_const_atTop_of_pos hδ).mpr hk)
  have he := Real.tendsto_exp_atBot.comp hneg
  have hden := ((tendsto_const_nhds (x := (1 : ℝ))).sub he).pow 2
  have hh := (tendsto_const_nhds (x := Real.sqrt ρ)).div hden (by norm_num : (1 - 0 : ℝ) ^ 2 ≠ 0)
  norm_num only [sub_zero, one_pow, div_one] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  dsimp only [Pi.div_apply, Function.comp_def]
  rw [upperWeylCoefficient, Real.sqrt_mul ht.le]
  rw [div_right_comm, mul_div_cancel_left₀ _ (Real.sqrt_pos.mpr ht).ne']

/-- The exact lower compliance comparison has the expected Weyl limit. -/
theorem lowerWeyl_defect_tendsto {δ ρ : ℝ} :
    Tendsto (fun t ↦ Real.sqrt t * lowerWeylCoefficient δ ρ t /
      (t + lowerWeylCoefficient δ ρ t)) atTop (𝓝 (Real.sqrt ρ)) :=
  weyl_quotient_tendsto (lowerWeylCoefficient_scaled_tendsto (δ := δ) (ρ := ρ))

/-- The exact compact-trial compliance comparison has the same Weyl limit. -/
theorem upperWeyl_defect_tendsto {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) :
    Tendsto (fun t ↦ Real.sqrt t * upperWeylCoefficient δ ρ t /
      (t + upperWeylCoefficient δ ρ t)) atTop (𝓝 (Real.sqrt ρ)) :=
  weyl_quotient_tendsto (upperWeylCoefficient_scaled_tendsto hδ hρ)

/-- The elementary lower coefficient is nonnegative eventually. -/
theorem lowerWeylCoefficient_eventually_nonneg {δ ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ t : ℝ in atTop, 0 ≤ lowerWeylCoefficient δ ρ t := by
  have hh : Tendsto (fun t : ℝ ↦ Real.sqrt (t * ρ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp ((tendsto_mul_const_atTop_of_pos hρ).mpr tendsto_id)
  exact (hh.eventually (eventually_ge_atTop (1 / δ))).mono fun t ht ↦ sub_nonneg.mpr ht

/-- The linear-test coefficient satisfies the precise local energy
constraint whenever its scale parameter is nonnegative. -/
theorem lowerWeylCoefficient_energy_bound {δ ρ t : ℝ} (hδ : 0 < δ) (hρ : 0 ≤ ρ) (ht : 0 ≤ t) :
    (lowerWeylCoefficient δ ρ t) ^ 2 + lowerWeylCoefficient δ ρ t / δ ≤ t * ρ := by
  have hs := Real.sq_sqrt (mul_nonneg ht hρ)
  have hp : 0 ≤ Real.sqrt (t * ρ) / δ := div_nonneg (Real.sqrt_nonneg _) hδ.le
  dsimp only [lowerWeylCoefficient]
  generalize hbdef : Real.sqrt (t * ρ) = b at *
  have he : (b - 1 / δ) ^ 2 + (b - 1 / δ) / δ = t * ρ - b / δ := by
    rw [← hs]
    ring
  rw [he]
  exact sub_le_self _ hp

end
end krylov.Strings.GeneralSpectral
