import polyak.ModeLocking.Localization.Atom
import polyak.ModeLocking.Localization.RatioBound

/-! Global in the shift: compact quadratic coercivity of the base symbol
implies the stated second-moment bound for every later feasible measure. -/
noncomputable section
namespace polyak.ModeLocking.Localization
open Levels MeasureTheory Set
open scoped BigOperators
variable {I : Type*} [Fintype I]

theorem quadratic_localization_of_coercivity (q : General.Tuning) (t : ℝ) (n : I → ℤ)
    (a : I → ℝ) (γ : ℝ) (ha : ∀ i, 0 ≤ a i) (hγ : 0 ≤ γ)
    (hnorm : (∑ i, a i)+γ=1) (ρ : Frequency → ℝ) (hρ : Continuous ρ)
    (hbound : ∀ ω, 0 ≤ ρ ω ∧ ρ ω ≤ Real.pi)
    (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hcoercive : ∀ ω, c₀*(ρ ω)^2 ≤ -symbol q t n a γ ω) :
    ∃ c > 0, ∀ s, t ≤ s → ∀ w : Measure Frequency, IsFiniteMeasure w →
      (0 ≤ ∫ ω, symbol q s n a γ ω ∂w) →
      (∫ ω, (ρ ω)^2 ∂w) ≤ (2*(s-t)/c)*w.real univ := by
  let c : ℝ := min (c₀/2) (2/Real.pi^2)
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  have hcle : c ≤ c₀/2 := min_le_left _ _
  have hcpi : c*Real.pi^2 ≤ 2 := by
    have he : c ≤ 2/Real.pi^2 := min_le_right _ _
    exact (le_div_iff₀ (sq_pos_of_pos Real.pi_pos)).mp he
  refine ⟨c,hc,?_⟩
  intro s hst w hw hfeas
  let : IsFiniteMeasure w := hw
  have hiρ : Integrable (fun ω => (ρ ω)^2) w :=
    (hρ.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hm : 0 ≤ w.real univ := ENNReal.toReal_nonneg
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hc).mpr
  by_cases hs : s-t ≤ 1
  · have hD : Integrable (defect q s t n a γ) w :=
      (continuous_defect q s t n a γ).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hpoint (ω : Frequency) : c*(ρ ω)^2 ≤ defect q s t n a γ ω := by
      have hr := sineRatio_ge_half q s t ω (by rw [abs_of_nonneg (sub_nonneg.mpr hst)]; exact hs)
      have hT := hcoercive ω
      have hnonneg : 0 ≤ -symbol q t n a γ ω := le_trans (by positivity) hT
      have hmul := mul_le_mul_of_nonneg_right hr hnonneg
      unfold defect
      nlinarith [sq_nonneg (ρ ω)]
    have hi := integral_mono (hiρ.const_mul c) hD hpoint
    rw [integral_const_mul] at hi
    have hb := localization_mass_bound q s t n a γ ha hγ hnorm hst hfeas
    nlinarith
  · have hpoint (ω : Frequency) : (ρ ω)^2 ≤ Real.pi^2 := by
      nlinarith [(hbound ω).1,(hbound ω).2,Real.pi_pos]
    have hi := integral_mono hiρ (integrable_const (Real.pi^2)) hpoint
    simp only [integral_const,smul_eq_mul] at hi
    have hp := mul_le_mul_of_nonneg_left hi hc.le
    have hpp := mul_le_mul_of_nonneg_right hcpi hm
    nlinarith

end polyak.ModeLocking.Localization
