import krylov.Strings.OptimizerTypeClock
import krylov.Strings.OptimizerEndpointData
import krylov.ContinuumControl.EndpointOrbitValue

/-!
Article: main_krylov, thm:value and apC:prop:g1, actual endpoint attainment.
Use: integrate the exact Bellman potential along the constructed global LV
orbit after the genuine physical clock inversion, then pass to the full
nonnegative reward. No global optimizer or terminal condition is assumed.
Source: the proved endpoint orbit, quadratures and monotone convergence.
-/

namespace krylov.Strings.OptimizerQuadratures
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

/-- The endpoint potential of the genuinely constructed physical state. -/
def physicalEndpointValue (s U : ℝ → ℝ) (x : ℝ) : ℝ :=
  krylov.ContinuumControl.endpointOrbitValue (s (inverseClock s x))
    (U (inverseClock s x)) (expPrimitive U (inverseClock s x))

/-- The reward density written in the globally continuous physical extension. -/
def endpointRewardRate (s U : ℝ → ℝ) (x : ℝ) : ℝ :=
  (extendedEnergy s U x)⁻¹ * extendedDensity s x

/-- The endpoint physical reward rate is continuous. -/
theorem endpointRewardRate_continuous {s U : ℝ → ℝ} (hs : Continuous s)
    (hU : Continuous U) (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t) :
    Continuous (endpointRewardRate s U) := by
  obtain ⟨_, _, hK⟩ := extended_coordinates_continuous hs hU hp h₁
  exact (hK.inv₀ (fun _ ↦ (expPrimitive_pos _ _).ne')).mul
    (extendedDensity_continuous hs hp h₁)

/-- The endpoint physical reward rate is nonnegative. -/
theorem endpointRewardRate_nonneg {s U : ℝ → ℝ} (hp : ∀ t, 0 < s t) (x : ℝ) :
    0 ≤ endpointRewardRate s U x := by
  exact mul_nonneg (inv_nonneg.mpr (expPrimitive_pos _ _).le) (extendedDensity_pos hp x).le

/-- Positive physical positions correspond to positive LV times. -/
theorem inverseClock_pos {s : ℝ → ℝ} (hs : Continuous s)
    (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t) {x : ℝ} (hx : 0 < x) :
    0 < inverseClock s x := by
  apply (physicalClock_strictMono hs hp).lt_iff_lt.mp
  simpa only [physicalClock_zero, inverseClock,
    inverseClock_right_inverse hs hp h₁ hx.le] using hx

/-- The endpoint potential is continuous on the source physical half-line. -/
theorem physicalEndpointValue_continuousOn {s U : ℝ → ℝ} (hs : Continuous s)
    (hU : Continuous U) (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t)
    (hUp : ∀ t ≥ 0, 0 < U t) :
    ContinuousOn (physicalEndpointValue s U) (Ici 0) := by
  intro x hx
  have hi : ContinuousAt (inverseClock s) x :=
    (inverseClock_derivative_nonneg hs hp h₁ hx).continuousAt
  have hsx : ContinuousAt (fun y ↦ s (inverseClock s y)) x := hs.continuousAt.comp hi
  have hUx : ContinuousAt (fun y ↦ U (inverseClock s y)) x := hU.continuousAt.comp hi
  have hKx : ContinuousAt (fun y ↦ expPrimitive U (inverseClock s y)) x :=
    (expPrimitive_continuous hU).continuousAt.comp hi
  exact (((hUx.add hsx).sub continuousAt_const).div
    ((((hUx.const_mul 2).mul hsx.sqrt).mul hKx))
    (by have hUpos := hUp _ (inverseClock_nonneg hs hp h₁ hx)
        have hspos := Real.sqrt_pos.mpr (hp (inverseClock s x))
        have hKpos := expPrimitive_pos U (inverseClock s x)
        exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hUpos.ne')
          hspos.ne') hKpos.ne')).continuousWithinAt

/-- The physical derivative is exactly minus the actual smooth reward rate. -/
theorem physicalEndpointValue_derivative {s U : ℝ → ℝ} (hs : Continuous s)
    (hU : Continuous U) (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t)
    (hUp : ∀ t ≥ 0, 0 < U t)
    (hode : ∀ t > 0, HasDerivAt s (2 * s t * (s t - 1 - U t)) t ∧
      HasDerivAt U (U t * (s t + 1 - U t)) t)
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (physicalEndpointValue s U) (-endpointRewardRate s U x) x := by
  let t := inverseClock s x
  have ht : 0 < t := inverseClock_pos hs hp h₁ hx
  have hd := (krylov.ContinuumControl.hasDerivAt_endpointOrbitValue
    (hp t) (hUp t ht.le) (expPrimitive_pos U t) (hode t ht).1 (hode t ht).2
    (expPrimitive_derivative hU t)).comp x (inverseClock_derivative_nonneg hs hp h₁ hx.le)
  convert hd using 1
  · rfl
  · obtain ⟨_, _, hK, hv⟩ := extended_coordinates_eq (U := U) hs hp hx.le
    dsimp [endpointRewardRate]
    rw [hK, hv]
    dsimp [physicalEnergy, physicalDensity, physicalPosition, physicalSlope, physicalSpeed]
    change -((expPrimitive U t)⁻¹ *
        (Real.exp t / (expPrimitive s t * Real.sqrt (s t)))) =
      (-Real.sqrt (s t) / expPrimitive U t) *
        (expPrimitive s t * s t / Real.exp t)⁻¹
    have hsqrt := Real.sq_sqrt (hp t).le
    field_simp [(expPrimitive_pos U t).ne', (expPrimitive_pos s t).ne',
      (hp t).ne', (Real.sqrt_pos.mpr (hp t)).ne']
    nlinarith

/-- Every physical prefix has its exact potential-drop formula. -/
theorem endpointRewardRate_integral {s U : ℝ → ℝ} (hs : Continuous s)
    (hU : Continuous U) (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t)
    (hUp : ∀ t ≥ 0, 0 < U t)
    (hode : ∀ t > 0, HasDerivAt s (2 * s t * (s t - 1 - U t)) t ∧
      HasDerivAt U (U t * (s t + 1 - U t)) t)
    {x : ℝ} (hx : 0 ≤ x) :
    ∫ t in (0 : ℝ)..x, endpointRewardRate s U t =
      physicalEndpointValue s U 0 - physicalEndpointValue s U x := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx
    ((physicalEndpointValue_continuousOn hs hU hp h₁ hUp).mono
      (fun _ ht ↦ ht.1))
    (fun t ht ↦ physicalEndpointValue_derivative hs hU hp h₁ hUp hode ht.1)
    ((endpointRewardRate_continuous hs hU hp h₁).neg.intervalIntegrable 0 x)
  rw [intervalIntegral.integral_neg] at h
  linarith

/-- The initial endpoint potential is half the square root of the shooting coordinate. -/
theorem physicalEndpointValue_initial {s U : ℝ → ℝ} (hs : Continuous s)
    (hp : ∀ t, 0 < s t) (hU₀ : U 0 = 1) :
    physicalEndpointValue s U 0 = Real.sqrt (s 0) / 2 := by
  dsimp [physicalEndpointValue]
  rw [inverseClock_zero hs hp, hU₀, expPrimitive_zero]
  dsimp [krylov.ContinuumControl.endpointOrbitValue]
  have hsq := Real.sq_sqrt (hp 0).le
  have hp₀ := (Real.sqrt_pos.mpr (hp 0)).ne'
  field_simp
  nlinarith

/-- A nonnegative orbit rate gives an exponential primitive at least one at nonnegative times. -/
theorem expPrimitive_ge_one {U : ℝ → ℝ} (hU : ∀ t ≥ 0, 0 ≤ U t)
    {t : ℝ} (ht : 0 ≤ t) : 1 ≤ expPrimitive U t := by
  apply Real.one_le_exp_iff.mpr
  exact intervalIntegral.integral_nonneg ht (fun u hu ↦ hU u hu.1)

/-- The terminal potential vanishes in actual physical length, not only in
the auxiliary LV clock. Both clocks were proved to reach infinity. -/
theorem physicalEndpointValue_tendsto_zero {s U : ℝ → ℝ} (hs : Continuous s)
    (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t)
    (hc : ∀ t ≥ 0, 1 ≤ U t ∧ U t + 1 ≤ s t ∧ s t ≤ 4 * U t)
    (hUinf : Tendsto U atTop atTop) :
    Tendsto (physicalEndpointValue s U) atTop (𝓝 0) := by
  have hterm := krylov.ContinuumControl.endpointOrbitValue_tendsto_zero
    (K := expPrimitive U) hUinf (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact ⟨(hc t ht).1, (hc t ht).2.1, (hc t ht).2.2,
        expPrimitive_ge_one (fun u hu ↦ le_trans zero_le_one (hc u hu).1) ht⟩)
  exact hterm.comp (inverseClock_tendsto_atTop hs hp h₁)

/-- The mass-based prefix reward is exactly the physical potential drop. -/
theorem constructedMass_rewardPrefix {s U : ℝ → ℝ} (hs : Continuous s)
    (hU : Continuous U) (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t)
    (hU₀ : U 0 = 1) (hUp : ∀ t ≥ 0, 0 < U t)
    (hode : ∀ t > 0, HasDerivAt s (2 * s t * (s t - 1 - U t)) t ∧
      HasDerivAt U (U t * (s t + 1 - U t)) t)
    {x : ℝ} (hx : 0 ≤ x) :
    (constructedMass s hs hp h₁).rewardPrefix 1 (extendedPosition s) x =
      ENNReal.ofReal (Real.sqrt (s 0) / 2 - physicalEndpointValue s U x) := by
  have ha := constructedMass_rewardDensity hs hU hp h₁ hU₀
    (fun t ht ↦ (hode t ht).2) (⟨x, hx⟩ : ℝ≥0)
  have hi : IntegrableOn (endpointRewardRate s U) (Ioc 0 x) :=
    (endpointRewardRate_continuous hs hU hp h₁).integrableOn_Ioc
  have hnonneg : ∀ᵐ t ∂volume.restrict (Ioc 0 x), 0 ≤ endpointRewardRate s U t :=
    Eventually.of_forall (endpointRewardRate_nonneg hp)
  calc
    (constructedMass s hs hp h₁).rewardPrefix 1 (extendedPosition s) x =
        ∫⁻ t in Ioc 0 x, ENNReal.ofReal (endpointRewardRate s U t) := by
      exact lintegral_congr_ae (ha.fun_comp ENNReal.ofReal)
    _ = ENNReal.ofReal (∫ t in (0 : ℝ)..x, endpointRewardRate s U t) := by
      rw [intervalIntegral.integral_of_le hx]
      exact (ofReal_integral_eq_lintegral_ofReal hi hnonneg).symm
    _ = _ := by rw [endpointRewardRate_integral hs hU hp h₁ hUp hode hx,
        physicalEndpointValue_initial hs hp hU₀]

/-- Exact attainment by the constructed genuine global Stieltjes string.
The value comes from the actual RN-defined reward on the whole half-line. -/
theorem constructedMass_reward {s U : ℝ → ℝ} (hs : Continuous s)
    (hU : Continuous U) (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t)
    (hU₀ : U 0 = 1)
    (hode : ∀ t > 0, HasDerivAt s (2 * s t * (s t - 1 - U t)) t ∧
      HasDerivAt U (U t * (s t + 1 - U t)) t)
    (hc : ∀ t ≥ 0, 1 ≤ U t ∧ U t + 1 ≤ s t ∧ s t ≤ 4 * U t)
    (hUinf : Tendsto U atTop atTop) :
    (constructedMass s hs hp h₁).reward 1 (extendedPosition s) =
      ENNReal.ofReal (Real.sqrt (s 0) / 2) := by
  have hUp : ∀ t ≥ 0, 0 < U t := fun t ht ↦ lt_of_lt_of_le zero_lt_one (hc t ht).1
  have hterm := physicalEndpointValue_tendsto_zero hs hp h₁ hc hUinf
  have hlim : Tendsto (fun n : ℕ ↦
      (constructedMass s hs hp h₁).rewardPrefix 1 (extendedPosition s) n)
      atTop (𝓝 (ENNReal.ofReal (Real.sqrt (s 0) / 2))) := by
    have hn : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hr : Tendsto (fun n : ℕ ↦ Real.sqrt (s 0) / 2 - physicalEndpointValue s U n)
        atTop (𝓝 (Real.sqrt (s 0) / 2 - 0)) :=
      tendsto_const_nhds.sub (hterm.comp hn)
    have hl := (ENNReal.continuous_ofReal.tendsto (Real.sqrt (s 0) / 2 - 0)).comp hr
    simpa only [Function.comp_def, sub_zero, constructedMass_rewardPrefix hs hU hp h₁ hU₀ hUp hode
      (Nat.cast_nonneg _)] using hl
  rw [Mass.reward_eq_iSup_prefix]
  apply iSup_eq_of_tendsto _ hlim
  intro n m hnm
  exact (constructedMass s hs hp h₁).rewardPrefix_mono 1 (extendedPosition s)
    (by exact_mod_cast hnm)

/-- A genuine global endpoint optimizer exists. Its mass, state, type clock
and total reward are conclusions obtained from the proved global shooting
orbit. The initial shooting value lies strictly between two and four. -/
theorem exists_actual_global_endpoint_attainment :
    ∃ s₀ ∈ Ioo (2 : ℝ) 4, ∃ M : Mass, ∃ φ p K v : ℝ → ℝ,
      Continuous φ ∧ Continuous v ∧ φ 0 = 1 ∧ p 0 = 1 ∧ K 0 = 1 ∧
      (∀ x ≥ 0, krylov.ContinuumControl.SmoothStringAt φ p K v x) ∧
      (∀ x ≥ 0, φ x = 1 + ∫ t in Ioc 0 x, p t ∧
        p x = integralSlope M.measure φ x ∧ K x = integralEnergy M.measure φ x ∧
        M.typeClock x = ∫ t in (0 : ℝ)..x, v t) ∧
      Tendsto M.typeClock atTop atTop ∧ v 0 = 1 / Real.sqrt s₀ ∧
      HasDerivWithinAt M.cumulative s₀⁻¹ (Ici 0) 0 ∧
      M.reward 1 φ = ENNReal.ofReal (Real.sqrt s₀ / 2) := by
  obtain ⟨s, U, hs, hU, hU₀, hs₂, hode, hc⟩ := exists_endpoint_data
  have hp : ∀ t, 0 < s t := fun t ↦ lt_of_lt_of_le (by norm_num) (hs₂ t)
  have h₁ : ∀ t ≥ 0, 1 ≤ s t := fun t _ ↦ by linarith [hs₂ t]
  have hcorr : ∀ t ≥ 0, 1 ≤ U t ∧ U t + 1 ≤ s t ∧ s t ≤ 4 * U t := by
    intro t ht
    have he : 1 ≤ Real.exp (2 * t) := Real.one_le_exp_iff.mpr (by positivity)
    exact ⟨he.trans (hc t ht).2.2.2, (hc t ht).1.le, (hc t ht).2.2.1⟩
  have hUinf : Tendsto U atTop atTop := by
    apply tendsto_atTop_mono' atTop
      ((eventually_ge_atTop (0 : ℝ)).mono (fun t ht ↦ (hc t ht).2.2.2))
    exact Real.tendsto_exp_atTop.comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hs₀ : s 0 ∈ Ioo (2 : ℝ) 4 := by
    obtain ⟨hl, hr, _⟩ := hc 0 le_rfl
    rw [hU₀] at hl hr
    exact ⟨by linarith, by linarith⟩
  obtain ⟨hφ, _, _⟩ := extended_coordinates_continuous hs hU hp h₁
  obtain ⟨hφ₀, hp₀, hK₀⟩ := extended_initial (U := U) hs hp
  refine ⟨s 0, hs₀, constructedMass s hs hp h₁, extendedPosition s,
    extendedSlope s, extendedEnergy s U, extendedDensity s, hφ,
    extendedDensity_continuous hs hp h₁, hφ₀, hp₀, hK₀, ?_, ?_,
    constructedMass_typeClock_tendsto_atTop hs hp h₁, extendedDensity_initial hs hp,
    constructedMass_right_derivative hs hp h₁, ?_⟩
  · intro x hx
    exact extended_smoothStringAt hs hU hp h₁ hU₀ (fun t ht ↦ (hode t ht).2) hx
  · intro x hx
    obtain ⟨hφx, hpx, hKx⟩ := constructedMass_state hs hU hp h₁ hU₀
      (fun t ht ↦ (hode t ht).2) hx
    exact ⟨hφx, hpx, hKx, constructedMass_typeClock hs hp h₁ hx⟩
  · exact constructedMass_reward hs hU hp h₁ hU₀ hode hcorr hUinf

end
end krylov.Strings.OptimizerQuadratures
