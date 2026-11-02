import krylov.Strings.OptimizerOrbitAttainment
import krylov.Strings.FeedbackMass

/-!
Article: main_krylov, thm:value, shape and total mass.
Use: compute the actual constructed mass in LV time and establish its exact
half-gamma conservation law and the required terminal decay.
Source: FTC for the actual density mass and the printed LV cancellation.
-/

namespace krylov.Strings.OptimizerQuadratures
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

/-- The smooth LV-time representative of the actual cumulative mass. -/
def orbitMass (s : ℝ → ℝ) (t : ℝ) : ℝ :=
  1 + primitive (fun x ↦ extendedDensity s x ^ 2) (physicalClock s t)

/-- The auxiliary mass coordinate in actual quadrature coordinates. -/
def orbitMassCoordinate (s U : ℝ → ℝ) (t : ℝ) : ℝ :=
  feedbackMassCoordinate (s t) (expPrimitive U t) (expPrimitive s t)

/-- The accumulated physical mass is continuous in LV time. -/
theorem orbitMass_continuous {s : ℝ → ℝ} (hs : Continuous s)
    (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t) : Continuous (orbitMass s) := by
  have hf := continuous_iff_continuousAt.mpr (fun x ↦
    (primitive_derivative ((extendedDensity_continuous hs hp h₁).pow 2) x).continuousAt)
  have hX := continuous_iff_continuousAt.mpr (fun x ↦ (physicalClock_derivative hs x).continuousAt)
  exact continuous_const.add (hf.comp hX)

/-- The LV mass quadrature equals the actual cumulative mass at the physical clock. -/
theorem constructedMass_cumulative_at_physicalClock {s : ℝ → ℝ} (hs : Continuous s)
    (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t) {t : ℝ} (ht : 0 ≤ t) :
    (constructedMass s hs hp h₁).cumulative (physicalClock s t) = orbitMass s t := by
  have hXt : 0 ≤ physicalClock s t := by
    simpa only [physicalClock_zero] using (physicalClock_strictMono hs hp).monotone ht
  exact OptimizerDensity.globalCumulative_eq _ (extendedDensity_continuous hs hp h₁) hXt

/-- The actual mass increment in LV time is `p/φ`. -/
theorem orbitMass_derivative {s : ℝ → ℝ} (hs : Continuous s)
    (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (orbitMass s) (Real.exp t / expPrimitive s t) t := by
  have hXt : 0 ≤ physicalClock s t := by
    simpa only [physicalClock_zero] using (physicalClock_strictMono hs hp).monotone ht
  have hd := ((primitive_derivative ((extendedDensity_continuous hs hp h₁).pow 2)
    (physicalClock s t)).comp t (physicalClock_derivative hs t)).const_add 1
  convert hd using 1
  · rfl
  · obtain ⟨_, _, _, hv⟩ := extended_coordinates_eq (U := s) hs hp hXt
    dsimp only [Pi.pow_apply]
    rw [hv]
    have hinv : inverseClock s (physicalClock s t) = t :=
      Function.leftInverse_invFun (physicalClock_strictMono hs hp).injective t
    simp only [physicalDensity, physicalSlope, physicalPosition, hinv]
    dsimp [physicalSpeed]
    field_simp [(expPrimitive_pos s t).ne', (hp t).ne',
      (Real.sqrt_pos.mpr (hp t)).ne']
    rw [Real.sq_sqrt (hp t).le]

/-- The LV mass quadrature starts with the distinguished unit origin atom. -/
@[simp] theorem orbitMass_zero (s : ℝ → ℝ) : orbitMass s 0 = 1 := by simp [orbitMass]

/-- The auxiliary feedback mass coordinate is continuous along the quadrature state. -/
theorem orbitMassCoordinate_continuous {s U : ℝ → ℝ} (hs : Continuous s) (hU : Continuous U) :
    Continuous (orbitMassCoordinate s U) :=
  ((hs.sub continuous_const).mul (expPrimitive_continuous hU)).div
    ((expPrimitive_continuous hs).pow 2) (fun t ↦ pow_ne_zero 2 (expPrimitive_pos s t).ne')

/-- The auxiliary mass coordinate satisfies the source balance derivative along the LV equations. -/
theorem orbitMassCoordinate_derivative {γ : ℝ} {s U : ℝ → ℝ}
    (hs : Continuous s) (hU : Continuous U) {t : ℝ}
    (hds : HasDerivAt s (2 * s t * (s t - 1 - γ * U t)) t) :
    HasDerivAt (orbitMassCoordinate s U)
      (expPrimitive U t * U t / expPrimitive s t ^ 2 * ((1 - 2 * γ) * s t - 1)) t := by
  have hd := ((hds.sub_const 1).mul (expPrimitive_derivative hU t)).div
    ((expPrimitive_derivative hs t).pow 2) (pow_ne_zero 2 (expPrimitive_pos s t).ne')
  convert hd using 1
  · rfl
  · dsimp
    field_simp
    ring

/-- The half-gamma balance is derived along the actually constructed
quadratures, with their actual cumulative mass. -/
theorem orbit_half_mass_balance {s U : ℝ → ℝ} (hs : Continuous s) (hU : Continuous U)
    (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t) (hU₀ : U 0 = 1)
    (hode : ∀ t > 0, HasDerivAt s (2 * s t * (s t - 1 - (1 / 2 : ℝ) * U t)) t ∧
      HasDerivAt U (U t * (s t + 1 - U t)) t)
    {t : ℝ} (ht : 0 ≤ t) : orbitMass s t + orbitMassCoordinate s U t = s 0 := by
  have hd (u : ℝ) (hu : 0 < u) :
      HasDerivAt (fun u ↦ orbitMass s u + orbitMassCoordinate s U u) 0 u := by
    have hm := orbitMass_derivative hs hp h₁ hu.le
    have hH := orbitMassCoordinate_derivative hs hU (hode u hu).1
    have hr := coordinate_ratio hs hU hU₀ (fun t ht ↦ (hode t ht).2) hu.le
    convert hm.add hH using 1
    dsimp [stateRatio] at hr
    rw [hr]
    field_simp [(expPrimitive_pos U u).ne', (expPrimitive_pos s u).ne']
    ring
  have hc := (orbitMass_continuous hs hp h₁).add (orbitMassCoordinate_continuous hs hU)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hc.continuousOn
    (fun u hu ↦ hd u hu.1) intervalIntegrable_const
  have hz : orbitMass s 0 + orbitMassCoordinate s U 0 = s 0 := by
    simp only [orbitMass_zero, orbitMassCoordinate, expPrimitive_zero]
    exact feedback_mass_initial (s 0)
  simpa only [intervalIntegral.integral_zero, Pi.add_apply, hz, sub_eq_zero] using hi.symm

/-- A primitive with an eventually strictly negative limiting rate tends
to minus infinity. This supplies the terminal mass-coordinate decay. -/
theorem primitive_tendsto_atBot_of_neg_limit {f : ℝ → ℝ} {c : ℝ}
    (hc : Continuous f) (hf : Tendsto f atTop (𝓝 c)) (hneg : c < 0) :
    Tendsto (primitive f) atTop atBot := by
  have hev : ∀ᶠ t in atTop, f t ≤ c / 2 :=
    ((tendsto_order.1 hf).2 (c / 2) (by linarith)).mono (fun _ ht ↦ ht.le)
  obtain ⟨a, ha⟩ := eventually_atTop.1 hev
  have hlim : Tendsto (fun t : ℝ ↦ c / 2 * t + (primitive f a - c / 2 * a)) atTop atBot :=
    tendsto_atBot_add_const_right atTop _
      (Tendsto.const_mul_atTop_of_neg (by linarith : c / 2 < 0) tendsto_id)
  apply tendsto_atBot_mono' atTop _ hlim
  filter_upwards [eventually_ge_atTop a] with t ht
  have hsplit : primitive f t = primitive f a + ∫ u in a..t, f u :=
    (intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 a)
      (hc.intervalIntegrable a t)).symm
  have hm := intervalIntegral.integral_mono_on ht (hc.intervalIntegrable a t)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ c / 2) volume a t)
    (fun u hu ↦ ha u hu.1)
  rw [hsplit]
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hm
  linarith

/-- The energy-to-squared-position ratio is the exponential primitive of its logarithmic orbit rate. -/
theorem energy_position_ratio_eq_expPrimitive {s U : ℝ → ℝ}
    (hs : Continuous s) (hU : Continuous U) (t : ℝ) :
    expPrimitive U t / expPrimitive s t ^ 2 = expPrimitive (fun u ↦ U u - 2 * s u) t := by
  have hi := intervalIntegral.integral_sub (μ := volume) (hU.intervalIntegrable 0 t)
    ((hs.const_mul 2).intervalIntegrable 0 t)
  simp only [intervalIntegral.integral_const_mul] at hi
  dsimp [expPrimitive, primitive]
  rw [hi, Real.exp_sub]
  rw [show Real.exp (2 * ∫ u in (0 : ℝ)..t, s u) =
    Real.exp (∫ u in (0 : ℝ)..t, s u) ^ 2 from Real.exp_nat_mul _ 2]

/-- Terminal decay of the actual auxiliary mass coordinate follows from
the limiting LV state, with no separately assumed mass balance at infinity. -/
theorem orbitMassCoordinate_tendsto_zero {s U : ℝ → ℝ} {sLim ULim : ℝ}
    (hs : Continuous s) (hU : Continuous U)
    (hsinf : Tendsto s atTop (𝓝 sLim)) (hUinf : Tendsto U atTop (𝓝 ULim))
    (hgap : ULim - 2 * sLim < 0) :
    Tendsto (orbitMassCoordinate s U) atTop (𝓝 0) := by
  have hrate : Tendsto (fun t ↦ U t - 2 * s t) atTop (𝓝 (ULim - 2 * sLim)) :=
    hUinf.sub (hsinf.const_mul 2)
  have hratio : Tendsto (fun t ↦ expPrimitive U t / expPrimitive s t ^ 2) atTop (𝓝 0) := by
    have hh := Real.tendsto_exp_atBot.comp
      (primitive_tendsto_atBot_of_neg_limit (hU.sub (hs.const_mul 2)) hrate hgap)
    simp_rw [energy_position_ratio_eq_expPrimitive hs hU]
    exact hh
  have h := (hsinf.sub_const 1).mul hratio
  simp only [mul_zero] at h
  convert h using 1
  funext t
  dsimp [orbitMassCoordinate, feedbackMassCoordinate]
  ring

/-- The actual half-gamma mass tends to the initial shooting coordinate. -/
theorem constructedMass_half_total_mass {s U : ℝ → ℝ}
    (hs : Continuous s) (hU : Continuous U) (hp : ∀ t, 0 < s t)
    (h₁ : ∀ t ≥ 0, 1 ≤ s t) (hU₀ : U 0 = 1)
    (hode : ∀ t > 0, HasDerivAt s (2 * s t * (s t - 1 - (1 / 2 : ℝ) * U t)) t ∧
      HasDerivAt U (U t * (s t + 1 - U t)) t)
    (hsinf : Tendsto s atTop (𝓝 3)) (hUinf : Tendsto U atTop (𝓝 4)) :
    Tendsto (constructedMass s hs hp h₁).cumulative atTop (𝓝 (s 0)) := by
  have hH := orbitMassCoordinate_tendsto_zero hs hU hsinf hUinf (by norm_num : (4 : ℝ) - 2 * 3 < 0)
  have hm := feedback_total_mass_of_terminal_decay
    (fun t ht ↦ orbit_half_mass_balance hs hU hp h₁ hU₀ hode ht) hH
  have hlim := hm.comp (inverseClock_tendsto_atTop hs hp h₁)
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  have ht := inverseClock_nonneg hs hp h₁ hx
  have heq := constructedMass_cumulative_at_physicalClock hs hp h₁ ht
  rw [inverseClock_right_inverse hs hp h₁ hx] at heq
  exact heq.symm

end
end krylov.Strings.OptimizerQuadratures
