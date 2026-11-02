import krylov.Strings.OptimizerEndpointAttainment
import krylov.Strings.OptimizerSubcriticalData
import krylov.ContinuumControl.OrbitValue

/-!
Article: main_krylov, thm:value, subcritical global attainment.
Use: turn the actually constructed global stable LV orbit into an actual
global Stieltjes string and integrate its Bellman reward to infinity.
Source: the proved logistic shooting orbit, physical quadratures, exact
orbit-potential differentiation and nonnegative monotone convergence.
-/

namespace krylov.Strings.OptimizerQuadratures
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

/-- The gamma-dependent orbit potential evaluated at the inverse physical clock. -/
def physicalOrbitValue (γ : ℝ) (s U : ℝ → ℝ) (x : ℝ) : ℝ :=
  krylov.ContinuumControl.orbitValue γ (s (inverseClock s x))
    (U (inverseClock s x)) (expPrimitive U (inverseClock s x))

/-- The continuous physical reward rate built from the actual energy and density quadratures. -/
def orbitRewardRate (γ : ℝ) (s U : ℝ → ℝ) (x : ℝ) : ℝ :=
  extendedEnergy s U x ^ (-γ) * extendedDensity s x

/-- The gamma-dependent physical reward rate is continuous. -/
theorem orbitRewardRate_continuous {s U : ℝ → ℝ} (γ : ℝ) (hs : Continuous s)
    (hU : Continuous U) (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t) :
    Continuous (orbitRewardRate γ s U) := by
  obtain ⟨_, _, hK⟩ := extended_coordinates_continuous hs hU hp h₁
  exact (hK.rpow_const (fun _ ↦ Or.inl (expPrimitive_pos _ _).ne')).mul
    (extendedDensity_continuous hs hp h₁)

/-- The gamma-dependent physical reward rate is nonnegative. -/
theorem orbitRewardRate_nonneg {s U : ℝ → ℝ} (γ : ℝ) (hp : ∀ t, 0 < s t) (x : ℝ) :
    0 ≤ orbitRewardRate γ s U x :=
  mul_nonneg (Real.rpow_nonneg (expPrimitive_pos _ _).le _) (extendedDensity_pos hp x).le

/-- The orbit potential is continuous on the source physical half-line. -/
theorem physicalOrbitValue_continuousOn {γ : ℝ} (hγ : γ ≠ 0) {s U : ℝ → ℝ}
    (hs : Continuous s) (hU : Continuous U) (hp : ∀ t, 0 < s t)
    (h₁ : ∀ t ≥ 0, 1 ≤ s t) (hUp : ∀ t ≥ 0, 0 < U t) :
    ContinuousOn (physicalOrbitValue γ s U) (Ici 0) := by
  intro x hx
  have hi : ContinuousAt (inverseClock s) x :=
    (inverseClock_derivative_nonneg hs hp h₁ hx).continuousAt
  have hsx : ContinuousAt (fun y ↦ s (inverseClock s y)) x := hs.continuousAt.comp hi
  have hUx : ContinuousAt (fun y ↦ U (inverseClock s y)) x := hU.continuousAt.comp hi
  have hKx : ContinuousAt (fun y ↦ expPrimitive U (inverseClock s y)) x :=
    (expPrimitive_continuous hU).continuousAt.comp hi
  exact (((hKx.rpow_const (Or.inl (expPrimitive_pos _ _).ne')).mul
    ((hUx.add hsx).sub continuousAt_const)).div
    (((hUx.const_mul (2 * γ)).mul hsx.sqrt))
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hγ)
      (hUp _ (inverseClock_nonneg hs hp h₁ hx)).ne')
      (Real.sqrt_pos.mpr (hp _)).ne')).continuousWithinAt

/-- The physical potential decreases at exactly the physical reward rate along the LV equations. -/
theorem physicalOrbitValue_derivative {γ : ℝ} (hγ : γ ≠ 0) {s U : ℝ → ℝ}
    (hs : Continuous s) (hU : Continuous U) (hp : ∀ t, 0 < s t)
    (h₁ : ∀ t ≥ 0, 1 ≤ s t) (hUp : ∀ t ≥ 0, 0 < U t)
    (hode : ∀ t > 0, HasDerivAt s (2 * s t * (s t - 1 - γ * U t)) t ∧
      HasDerivAt U (U t * (s t + 1 - U t)) t)
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (physicalOrbitValue γ s U) (-orbitRewardRate γ s U x) x := by
  let t := inverseClock s x
  have ht : 0 < t := inverseClock_pos hs hp h₁ hx
  have hd := (krylov.ContinuumControl.hasDerivAt_orbitValue hγ
    (hp t) (hUp t ht.le) (expPrimitive_pos U t) (hode t ht).1 (hode t ht).2
    (expPrimitive_derivative hU t)).comp x (inverseClock_derivative_nonneg hs hp h₁ hx.le)
  convert hd using 1
  · rfl
  · obtain ⟨_, _, hK, hv⟩ := extended_coordinates_eq (U := U) hs hp hx.le
    dsimp [orbitRewardRate]
    rw [hK, hv]
    dsimp [physicalEnergy, physicalDensity, physicalPosition, physicalSlope, physicalSpeed]
    change -((expPrimitive U t) ^ (-γ) *
        (Real.exp t / (expPrimitive s t * Real.sqrt (s t)))) =
      (-Real.sqrt (s t) * expPrimitive U t ^ (-γ)) *
        (expPrimitive s t * s t / Real.exp t)⁻¹
    field_simp [(expPrimitive_pos s t).ne', (hp t).ne',
      (Real.sqrt_pos.mpr (hp t)).ne']
    rw [Real.sq_sqrt (hp t).le]

/-- The unit initial state gives the printed graph-crossing potential value. -/
theorem physicalOrbitValue_initial {γ : ℝ} {s U : ℝ → ℝ}
    (hs : Continuous s) (hp : ∀ t, 0 < s t) (hU₀ : U 0 = 1) :
    physicalOrbitValue γ s U 0 = Real.sqrt (s 0) / (2 * γ) := by
  dsimp [physicalOrbitValue]
  rw [inverseClock_zero hs hp, hU₀, expPrimitive_zero]
  exact krylov.ContinuumControl.orbitValue_initial γ (s 0) (hp 0)

/-- Reward on a finite physical interval equals its exact potential drop. -/
theorem orbitRewardRate_integral {γ : ℝ} (hγ : γ ≠ 0) {s U : ℝ → ℝ}
    (hs : Continuous s) (hU : Continuous U) (hp : ∀ t, 0 < s t)
    (h₁ : ∀ t ≥ 0, 1 ≤ s t) (hUp : ∀ t ≥ 0, 0 < U t)
    (hode : ∀ t > 0, HasDerivAt s (2 * s t * (s t - 1 - γ * U t)) t ∧
      HasDerivAt U (U t * (s t + 1 - U t)) t)
    {x : ℝ} (hx : 0 ≤ x) :
    ∫ t in (0 : ℝ)..x, orbitRewardRate γ s U t =
      physicalOrbitValue γ s U 0 - physicalOrbitValue γ s U x := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx
    ((physicalOrbitValue_continuousOn hγ hs hU hp h₁ hUp).mono (fun _ ht ↦ ht.1))
    (fun t ht ↦ physicalOrbitValue_derivative hγ hs hU hp h₁ hUp hode ht.1)
    ((orbitRewardRate_continuous γ hs hU hp h₁).neg.intervalIntegrable 0 x)
  rw [intervalIntegral.integral_neg] at h
  linarith

/-- The actual RN reward density agrees locally almost everywhere with the physical quadrature rate. -/
theorem constructedMass_rewardDensity_allGamma {s U : ℝ → ℝ} (γ : ℝ)
    (hs : Continuous s) (hU : Continuous U) (hp : ∀ t, 0 < s t)
    (h₁ : ∀ t ≥ 0, 1 ≤ s t) (hU₀ : U 0 = 1)
    (hode : ∀ t > 0, HasDerivAt U (U t * (s t + 1 - U t)) t) (L : ℝ≥0) :
    (constructedMass s hs hp h₁).rewardDensity γ (extendedPosition s) =ᵐ[
      volume.restrict (Ioc 0 (L : ℝ))] orbitRewardRate γ s U := by
  filter_upwards [constructedMass_typeDensity hs hp h₁ L,
    ae_restrict_mem measurableSet_Ioc] with x hx hxm
  obtain ⟨_, _, hK⟩ := constructedMass_state hs hU hp h₁ hU₀ hode hxm.1.le
  dsimp [Mass.rewardDensity, orbitRewardRate]
  rw [← hK, hx]

/-- An actual finite reward prefix equals initial potential minus terminal potential. -/
theorem constructedMass_rewardPrefix_allGamma {γ : ℝ} (hγ : γ ≠ 0) {s U : ℝ → ℝ}
    (hs : Continuous s) (hU : Continuous U) (hp : ∀ t, 0 < s t)
    (h₁ : ∀ t ≥ 0, 1 ≤ s t) (hU₀ : U 0 = 1) (hUp : ∀ t ≥ 0, 0 < U t)
    (hode : ∀ t > 0, HasDerivAt s (2 * s t * (s t - 1 - γ * U t)) t ∧
      HasDerivAt U (U t * (s t + 1 - U t)) t)
    {x : ℝ} (hx : 0 ≤ x) :
    (constructedMass s hs hp h₁).rewardPrefix γ (extendedPosition s) x =
      ENNReal.ofReal (Real.sqrt (s 0) / (2 * γ) - physicalOrbitValue γ s U x) := by
  have ha := constructedMass_rewardDensity_allGamma γ hs hU hp h₁ hU₀
    (fun t ht ↦ (hode t ht).2) (⟨x, hx⟩ : ℝ≥0)
  have hi : IntegrableOn (orbitRewardRate γ s U) (Ioc 0 x) :=
    (orbitRewardRate_continuous γ hs hU hp h₁).integrableOn_Ioc
  calc
    (constructedMass s hs hp h₁).rewardPrefix γ (extendedPosition s) x =
        ∫⁻ t in Ioc 0 x, ENNReal.ofReal (orbitRewardRate γ s U t) :=
      lintegral_congr_ae (ha.fun_comp ENNReal.ofReal)
    _ = ENNReal.ofReal (∫ t in (0 : ℝ)..x, orbitRewardRate γ s U t) := by
      rw [intervalIntegral.integral_of_le hx]
      exact (ofReal_integral_eq_lintegral_ofReal hi
        (Eventually.of_forall (orbitRewardRate_nonneg γ hp))).symm
    _ = _ := by rw [orbitRewardRate_integral hγ hs hU hp h₁ hUp hode hx,
        physicalOrbitValue_initial hs hp hU₀]

/-- Vanishing terminal potential gives actual infinite-horizon attainment of the crossing value. -/
theorem constructedMass_reward_allGamma {γ : ℝ} (hγ : γ ≠ 0) {s U : ℝ → ℝ}
    (hs : Continuous s) (hU : Continuous U) (hp : ∀ t, 0 < s t)
    (h₁ : ∀ t ≥ 0, 1 ≤ s t) (hU₀ : U 0 = 1) (hUp : ∀ t ≥ 0, 0 < U t)
    (hode : ∀ t > 0, HasDerivAt s (2 * s t * (s t - 1 - γ * U t)) t ∧
      HasDerivAt U (U t * (s t + 1 - U t)) t)
    (hterm : Tendsto (physicalOrbitValue γ s U) atTop (𝓝 0)) :
    (constructedMass s hs hp h₁).reward γ (extendedPosition s) =
      ENNReal.ofReal (Real.sqrt (s 0) / (2 * γ)) := by
  have hlim : Tendsto (fun n : ℕ ↦
      (constructedMass s hs hp h₁).rewardPrefix γ (extendedPosition s) n)
      atTop (𝓝 (ENNReal.ofReal (Real.sqrt (s 0) / (2 * γ)))) := by
    have hn : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hr : Tendsto (fun n : ℕ ↦ Real.sqrt (s 0) / (2 * γ) - physicalOrbitValue γ s U n)
        atTop (𝓝 (Real.sqrt (s 0) / (2 * γ) - 0)) :=
      tendsto_const_nhds.sub (hterm.comp hn)
    have hl := (ENNReal.continuous_ofReal.tendsto (Real.sqrt (s 0) / (2 * γ) - 0)).comp hr
    simpa only [Function.comp_def, sub_zero,
      constructedMass_rewardPrefix_allGamma hγ hs hU hp h₁ hU₀ hUp hode
        (Nat.cast_nonneg _)] using hl
  rw [Mass.reward_eq_iSup_prefix]
  apply iSup_eq_of_tendsto _ hlim
  intro n m hnm
  exact (constructedMass s hs hp h₁).rewardPrefix_mono γ (extendedPosition s)
    (by exact_mod_cast hnm)

/-- An orbit rate at least one forces its exponential energy quadrature to diverge. -/
theorem expPrimitive_tendsto_atTop {U : ℝ → ℝ} (hU : Continuous U)
    (hUone : ∀ t ≥ 0, 1 ≤ U t) : Tendsto (expPrimitive U) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ Real.tendsto_exp_atTop
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact Real.exp_le_exp.mpr (primitive_ge_self hU hUone ht)

/-- Actual global subcritical attainment, derived from the constructed
stable orbit. In particular the terminal-potential limit is proved from
saddle convergence and diverging energy, rather than assumed. -/
theorem exists_actual_global_subcritical_attainment {γ : ℝ}
    (hγ : 0 < γ) (hγ₁ : γ < 1) :
    ∃ s₀ : ℝ, 1 < s₀ ∧
      (∀ G : krylov.LotkaVolterra.SubcriticalGraph γ, s₀ = G.σ 1) ∧
      ∃ M : Mass, ∃ φ p K v : ℝ → ℝ,
      Continuous φ ∧ Continuous v ∧ φ 0 = 1 ∧ p 0 = 1 ∧ K 0 = 1 ∧
      (∀ x ≥ 0, krylov.ContinuumControl.SmoothStringAt φ p K v x) ∧
      (∀ x ≥ 0, φ x = 1 + ∫ t in Ioc 0 x, p t ∧
        p x = integralSlope M.measure φ x ∧ K x = integralEnergy M.measure φ x ∧
        M.typeClock x = ∫ t in (0 : ℝ)..x, v t) ∧
      Tendsto M.typeClock atTop atTop ∧ v 0 = 1 / Real.sqrt s₀ ∧
      HasDerivWithinAt M.cumulative s₀⁻¹ (Ici 0) 0 ∧
      M.reward γ φ = ENNReal.ofReal (Real.sqrt s₀ / (2 * γ)) := by
  obtain ⟨s, U, hs, hU, hU₀, hpos, hUone, _, hode, hsinf, hUinf, _, hcanonical, _⟩ :=
    exists_subcritical_data hγ hγ₁
  have hp : ∀ t, 0 < s t := fun t ↦ zero_lt_one.trans (hpos t).1
  have h₁ : ∀ t ≥ 0, 1 ≤ s t := fun t _ ↦ (hpos t).1.le
  have hUp : ∀ t ≥ 0, 0 < U t := fun t _ ↦ (hpos t).2
  have hd := fun t (_ : 0 < t) ↦ hode t
  have htermLV := krylov.ContinuumControl.orbitValue_tendsto_zero_of_finite_state
    hγ (krylov.LotkaVolterra.saddleS_pos hγ hγ₁) (krylov.LotkaVolterra.saddleU_pos hγ₁)
    hsinf hUinf (expPrimitive_tendsto_atTop hU hUone)
  have hterm : Tendsto (physicalOrbitValue γ s U) atTop (𝓝 0) :=
    htermLV.comp (inverseClock_tendsto_atTop hs hp h₁)
  obtain ⟨hφ, _, _⟩ := extended_coordinates_continuous hs hU hp h₁
  obtain ⟨hφ₀, hp₀, hK₀⟩ := extended_initial (U := U) hs hp
  refine ⟨s 0, (hpos 0).1, hcanonical, constructedMass s hs hp h₁, extendedPosition s,
    extendedSlope s, extendedEnergy s U, extendedDensity s, hφ,
    extendedDensity_continuous hs hp h₁, hφ₀, hp₀, hK₀, ?_, ?_,
    constructedMass_typeClock_tendsto_atTop hs hp h₁, extendedDensity_initial hs hp,
    constructedMass_right_derivative hs hp h₁, ?_⟩
  · intro x hx
    exact extended_smoothStringAt hs hU hp h₁ hU₀ (fun t ht ↦ (hd t ht).2) hx
  · intro x hx
    obtain ⟨hφx, hpx, hKx⟩ := constructedMass_state hs hU hp h₁ hU₀
      (fun t ht ↦ (hd t ht).2) hx
    exact ⟨hφx, hpx, hKx, constructedMass_typeClock hs hp h₁ hx⟩
  · exact constructedMass_reward_allGamma hγ.ne' hs hU hp h₁ hU₀ hUp hd hterm

/-- The full positive gamma range has actual global physical strings
attaining the corresponding shooting value, including the endpoint. -/
theorem exists_actual_global_attainment {γ : ℝ} (hγ : 0 < γ) (hγ₁ : γ ≤ 1) :
    ∃ s₀ : ℝ, 1 < s₀ ∧ ∃ M : Mass, ∃ φ p K v : ℝ → ℝ,
      Continuous φ ∧ Continuous v ∧ φ 0 = 1 ∧ p 0 = 1 ∧ K 0 = 1 ∧
      (∀ x ≥ 0, krylov.ContinuumControl.SmoothStringAt φ p K v x) ∧
      (∀ x ≥ 0, φ x = 1 + ∫ t in Ioc 0 x, p t ∧
        p x = integralSlope M.measure φ x ∧ K x = integralEnergy M.measure φ x ∧
        M.typeClock x = ∫ t in (0 : ℝ)..x, v t) ∧
      Tendsto M.typeClock atTop atTop ∧ v 0 = 1 / Real.sqrt s₀ ∧
      HasDerivWithinAt M.cumulative s₀⁻¹ (Ici 0) 0 ∧
      M.reward γ φ = ENNReal.ofReal (Real.sqrt s₀ / (2 * γ)) := by
  rcases eq_or_lt_of_le hγ₁ with rfl | hlt
  · obtain ⟨s₀, hs₀, M, φ, p, K, v, h⟩ := exists_actual_global_endpoint_attainment
    refine ⟨s₀, by linarith [hs₀.1], M, φ, p, K, v, ?_⟩
    simpa only [mul_one] using h
  · obtain ⟨s₀, hs₀, _, h⟩ := exists_actual_global_subcritical_attainment hγ hlt
    exact ⟨s₀, hs₀, h⟩

end
end krylov.Strings.OptimizerQuadratures
