import nesterov.Optimal.ModerateBand
import nesterov.Optimal.VanishingCoordinates
import nesterov.Optimal.RatioCriterion
import nesterov.Corner.VariableBand

/-! A bounded, nonvanishing ratio defect at unbounded deficit is detected by
actual spread spectra. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set
open scoped Topology
variable {A : Type*} {l : Filter A} (F : Scaling A l 3 2 (1/2))

theorem corner_moderate_dip_rest_lower {q M : ℝ} (hq : 0<q) (hq1 : q≤1)
    (hd : Tendsto F.cornerDefect l atTop)
    (hlo : ∀ᶠ a in l,q≤F.cornerCriterionRatio a)
    (hhi : ∀ᶠ a in l,F.cornerCriterionRatio a≤M)
    (hstable : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1) :
    ∀ᶠ a in l,1-(1-q/48)*F.epsilon a≤Momentum.momentumRestRate
      (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize
      (F.tuning a).step_pos.ne' (F.epsilon a^2) 1 := by
  let σ : A→ℝ := fun a=>(F.cornerDefect a)⁻¹
  let s : ℝ := min nesterov.Spread.canonicalKernel.s1 (1/20)
  let φ : ℝ := 3*q/4
  let K : A→ℕ := fun a=>Layer.rationalPeriod φ (σ a)
  have hσ : Tendsto σ l (𝓝[>] (0:ℝ)) := tendsto_inv_atTop_nhdsGT_zero.comp hd
  have hs : 0<s := lt_min nesterov.Spread.canonicalKernel.s1_pos (by norm_num)
  have hs1 : s≤nesterov.Spread.canonicalKernel.s1 := min_le_left _ _
  have hs20 : s≤1/20 := min_le_right _ _
  have hs6 : s∈Ioc (0:ℝ) (1/6) := ⟨hs,by linarith⟩
  have hφ : 0<φ := by dsimp [φ];positivity
  have ha : q/2<(1-s)^2*φ := by
    have hh : (2/3:ℝ)<(1-s)^2 := by nlinarith [hs.le,hs20]
    have hm := mul_lt_mul_of_pos_right hh hφ
    dsimp [φ] at hm ⊢
    nlinarith
  have hb : (1+s)^2*φ<q := by
    have hh : (1+s)^2<(4/3:ℝ) := by nlinarith [hs.le,hs20]
    have hm := mul_lt_mul_of_pos_right hh hφ
    dsimp [φ] at hm ⊢
    nlinarith
  have hsmall : Tendsto (fun a=>F.epsilon a/σ a^2) l (𝓝 0) := by
    have hn : ∀ᶠ a in l,0≤F.epsilon a*F.cornerDefect a^2 :=
      F.epsilon_pos.mono fun _ h=>mul_nonneg h.le (sq_nonneg _)
    have hub : ∀ᶠ a in l,F.epsilon a*F.cornerDefect a^2≤
        max M 1*(F.epsilon a*(F.stabilityMargin a+5+F.cornerDefect a)) := by
      filter_upwards [hhi,F.corner_denominator_pos hstable,F.epsilon_pos] with a hh hD he
      have hh' : F.cornerDefect a^2≤max M 1*(F.stabilityMargin a+5+F.cornerDefect a) := by
        exact (div_le_iff₀ hD).mp (hh.trans (le_max_left _ _))
      have hp := mul_le_mul_of_nonneg_left hh' he.le
      nlinarith only [hp]
    have hlim : Tendsto (fun a=>max M 1*(F.epsilon a*(F.stabilityMargin a+5+F.cornerDefect a)))
        l (𝓝 0) := by simpa only [mul_zero] using F.epsilon_cornerDenominator_tendsto.const_mul (max M 1)
    have ht := squeeze_zero' hn hub hlim
    simpa only [σ,inv_pow,div_inv_eq_mul] using ht
  have hsd : ∀ᶠ a in l,σ a*F.cornerDefect a=1 := by
    filter_upwards [hd.eventually_gt_atTop 0] with a ha
    exact inv_mul_cancel₀ ha.ne'
  have hD : ∀ᶠ a in l,q*(F.stabilityMargin a+5+F.cornerDefect a)≤F.cornerDefect a^2 := by
    filter_upwards [hlo,F.corner_denominator_pos hstable] with a ha hp
    exact (le_div_iff₀ hp).mp ha
  have hgeo := Layer.rational_band_geometry hσ hφ hs6 ha hb
  have hK : ∀ᶠ a in l,3≤K a := hgeo.1.mono fun _ h=>h.1
  have hband : ∀ᶠ a in l,∀ ω∈Spread.band s (nesterov.Spread.centerAngle (K a)),
      (1-Real.cos ω)/σ a∈Icc (q/2) q := by
    simpa only [K,nesterov.Spread.centerAngle] using hgeo.1.mono (fun _ h=>h.2)
  have hXi : Tendsto (fun a=>Spread.xiMax s (nesterov.Spread.centerAngle (K a))/σ a)
      l (𝓝 ((1+s)^2*φ)) := by
    simpa only [K,nesterov.Spread.centerAngle] using hgeo.2
  have heps := Layer.epsilon_div_cubic_at_scale hσ
    (by positivity : 0<(1+s)^2*φ) hXi hsmall
  exact F.corner_moderate_band_rest_lower hq hq1 hs hs1 hσ hsmall hsd hD hK hband heps hstable

end
end nesterov.TwoStep.Scaling
