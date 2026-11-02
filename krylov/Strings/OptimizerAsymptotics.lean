import krylov.Strings.OptimizerHalfMass
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
Article: main_krylov, thm:value, optimizer shape.
Use: turn the actual exponentially converging stable orbit into integrable
rate errors and positive limiting exponential amplitudes in actual type time.
Source: the exponential orbit estimate, ordinary improper-integral convergence
and continuity of exp and sqrt; no asymptotic ansatz is assumed.
-/

namespace krylov.Strings.OptimizerQuadratures
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

/-- Exponential decay makes the continuous orbit error integrable on positive LV time. -/
theorem exponential_error_integrable {f : ℝ → ℝ} {c C : ℝ} (hc : Continuous f)
    (hbound : ∀ t ≥ 0, |f t - c| ≤ C * Real.exp (-2 * t)) :
    IntegrableOn (fun t ↦ f t - c) (Ioi 0) := by
  apply ((integrableOn_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0) 0).const_mul C).mono'
    (hc.sub continuous_const).aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs]
  exact hbound t ht.le

/-- Integrable orbit errors yield convergent logarithmic amplitude errors. -/
theorem primitive_error_tendsto {f : ℝ → ℝ} {c C : ℝ} (hc : Continuous f)
    (hbound : ∀ t ≥ 0, |f t - c| ≤ C * Real.exp (-2 * t)) :
    Tendsto (fun t ↦ primitive f t - c * t) atTop
      (𝓝 (∫ t in Ioi (0 : ℝ), f t - c)) := by
  have h := intervalIntegral_tendsto_integral_Ioi 0
    (exponential_error_integrable hc hbound) tendsto_id
  convert h using 1
  funext t
  dsimp only [id_eq]
  rw [intervalIntegral.integral_sub (hc.intervalIntegrable 0 t) intervalIntegrable_const]
  simp only [primitive, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm]

/-- Above one, taking square roots does not increase the absolute difference. -/
theorem sqrt_difference_le {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    |Real.sqrt a - Real.sqrt b| ≤ |a - b| := by
  have hap : 0 ≤ a := zero_le_one.trans ha
  have hbp : 0 ≤ b := zero_le_one.trans hb
  have hra : 1 ≤ Real.sqrt a := Real.one_le_sqrt.mpr ha
  have hrb : 1 ≤ Real.sqrt b := Real.one_le_sqrt.mpr hb
  have hsa := Real.sq_sqrt hap
  have hsb := Real.sq_sqrt hbp
  rcases le_total a b with hab | hba
  · have hr := Real.sqrt_le_sqrt hab
    rw [abs_of_nonpos (sub_nonpos.mpr hr), abs_of_nonpos (sub_nonpos.mpr hab)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) (show 0 ≤ Real.sqrt a + Real.sqrt b - 1 by linarith)]
  · have hr := Real.sqrt_le_sqrt hba
    rw [abs_of_nonneg (sub_nonneg.mpr hr), abs_of_nonneg (sub_nonneg.mpr hba)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) (show 0 ≤ Real.sqrt a + Real.sqrt b - 1 by linarith)]

/-- The positive state's exponential error also bounds the square-root error. -/
theorem sqrt_exponential_error {s : ℝ → ℝ} {sLim C : ℝ}
    (h₁ : ∀ t ≥ 0, 1 ≤ s t) (hsLim : 1 ≤ sLim)
    (hbound : ∀ t ≥ 0, |s t - sLim| ≤ C * Real.exp (-2 * t)) :
    ∀ t ≥ 0, |Real.sqrt (s t) - Real.sqrt sLim| ≤ C * Real.exp (-2 * t) :=
  fun t ht ↦ (sqrt_difference_le (h₁ t ht) hsLim).trans (hbound t ht)

/-- Both actual logarithmic rates in type time tend to their printed
saddle values. The finite-state convergence used here is already proved
for the actual global subcritical shooting trajectory. -/
theorem type_logarithmic_rates_tendsto {γ sLim ULim : ℝ} {s U : ℝ → ℝ}
    (hsLim : 0 < sLim) (hs : Tendsto s atTop (𝓝 sLim)) (hU : Tendsto U atTop (𝓝 ULim)) :
    Tendsto (fun t ↦ U t / Real.sqrt (s t)) atTop (𝓝 (ULim / Real.sqrt sLim)) ∧
      Tendsto (fun t ↦ (2 - 2 * s t + γ * U t) / Real.sqrt (s t)) atTop
        (𝓝 ((2 - 2 * sLim + γ * ULim) / Real.sqrt sLim)) := by
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  exact ⟨hU.div hr (Real.sqrt_pos.mpr hsLim).ne',
    ((tendsto_const_nhds.sub (hs.const_mul 2)).add (hU.const_mul γ)).div hr
      (Real.sqrt_pos.mpr hsLim).ne'⟩

/-- The logarithmic density rate is derived from the actual feedback
quadratures and the concrete LV equation. -/
theorem log_densityInOrbitTime_derivative {γ : ℝ} {s U : ℝ → ℝ}
    (hs : Continuous s) {t : ℝ} (hp : 0 < s t)
    (hds : HasDerivAt s (2 * s t * (s t - 1 - γ * U t)) t) :
    HasDerivAt (fun u ↦ Real.log (densityInOrbitTime s u)) (2 - 2 * s t + γ * U t) t := by
  have hden : expPrimitive s t * Real.sqrt (s t) ≠ 0 :=
    mul_ne_zero (expPrimitive_pos s t).ne' (Real.sqrt_pos.mpr hp).ne'
  have hd := (Real.hasDerivAt_exp t).div
    ((expPrimitive_derivative hs t).mul (hds.sqrt hp.ne')) hden
  have hpos : 0 < densityInOrbitTime s t :=
    div_pos (Real.exp_pos _) (mul_pos (expPrimitive_pos _ _) (Real.sqrt_pos.mpr hp))
  have hlog := hd.log hpos.ne'
  convert hlog using 1
  · rfl
  · dsimp [densityInOrbitTime]
    field_simp [(expPrimitive_pos s t).ne', (Real.sqrt_pos.mpr hp).ne']
    rw [Real.sq_sqrt hp.le]
    ring

/-- The logarithmic energy quadrature has the actual orbit rate as its derivative. -/
theorem log_energy_quadrature_derivative {U : ℝ → ℝ} (hU : Continuous U) (t : ℝ) :
    HasDerivAt (fun u ↦ Real.log (expPrimitive U u)) (U t) t := by
  simpa only [expPrimitive, Real.log_exp] using primitive_derivative hU t

/-- The actual type clock has velocity sqrt(s); together with the preceding
two derivatives this justifies the logarithmic rates per unit type time. -/
theorem type_quadrature_derivative {s : ℝ → ℝ} (hs : Continuous s) (t : ℝ) :
    HasDerivAt (primitive (fun u ↦ Real.sqrt (s u))) (Real.sqrt (s t)) t :=
  primitive_derivative hs.sqrt t

/-- The type-time logarithmic rates tend to the printed subcritical saddle values. -/
theorem saddle_logarithmic_rates_tendsto {γ : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1)
    {s U : ℝ → ℝ}
    (hs : Tendsto s atTop (𝓝 (krylov.LotkaVolterra.saddleS γ)))
    (hU : Tendsto U atTop (𝓝 (krylov.LotkaVolterra.saddleU γ))) :
    Tendsto (fun t ↦ U t / Real.sqrt (s t)) atTop
        (𝓝 (krylov.LotkaVolterra.saddleU γ / Real.sqrt (krylov.LotkaVolterra.saddleS γ))) ∧
      Tendsto (fun t ↦ (2 - 2 * s t + γ * U t) / Real.sqrt (s t)) atTop
        (𝓝 (-(krylov.LotkaVolterra.saddleS γ - 1) /
          Real.sqrt (krylov.LotkaVolterra.saddleS γ))) := by
  have hh := type_logarithmic_rates_tendsto (γ := γ)
    (krylov.LotkaVolterra.saddleS_pos hγ hγ₁) hs hU
  have he : 2 - 2 * krylov.LotkaVolterra.saddleS γ + γ * krylov.LotkaVolterra.saddleU γ =
      -(krylov.LotkaVolterra.saddleS γ - 1) := by
    linarith [krylov.LotkaVolterra.saddleS_eq_one_add_mul_saddleU (ne_of_lt hγ₁)]
  simpa only [he] using hh

/-- Positive limiting exponential amplitudes for the energy and density,
with type time computed by the actual quadrature. This is stronger than
two-sided exponential comparability. -/
theorem orbit_exponential_amplitudes {γ sLim ULim C : ℝ} {s U : ℝ → ℝ}
    (hs : Continuous s) (hU : Continuous U) (hp : ∀ t, 0 < s t)
    (h₁ : ∀ t ≥ 0, 1 ≤ s t) (hsLim : 1 ≤ sLim)
    (hsinf : Tendsto s atTop (𝓝 sLim))
    (hsbound : ∀ t ≥ 0, |s t - sLim| ≤ C * Real.exp (-2 * t))
    (hUbound : ∀ t ≥ 0, |U t - ULim| ≤ C * Real.exp (-2 * t)) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      Tendsto (fun t ↦ expPrimitive U t ^ (-γ) /
        Real.exp (-(γ * ULim / Real.sqrt sLim) * primitive (fun u ↦ Real.sqrt (s u)) t))
        atTop (𝓝 a) ∧
      Tendsto (fun t ↦ densityInOrbitTime s t /
        Real.exp (-((sLim - 1) / Real.sqrt sLim) * primitive (fun u ↦ Real.sqrt (s u)) t))
        atTop (𝓝 b) := by
  let A := ∫ t in Ioi (0 : ℝ), U t - ULim
  let B := ∫ t in Ioi (0 : ℝ), s t - sLim
  let D := ∫ t in Ioi (0 : ℝ), Real.sqrt (s t) - Real.sqrt sLim
  have hA := primitive_error_tendsto hU hUbound
  have hB := primitive_error_tendsto hs hsbound
  have hD := primitive_error_tendsto hs.sqrt (sqrt_exponential_error h₁ hsLim hsbound)
  let cK := γ * ULim / Real.sqrt sLim
  let cv := (sLim - 1) / Real.sqrt sLim
  have hr : 0 < Real.sqrt sLim := Real.sqrt_pos.mpr (zero_lt_one.trans_le hsLim)
  refine ⟨Real.exp (-γ * A + cK * D), Real.exp (-B + cv * D) / Real.sqrt sLim,
    Real.exp_pos _, div_pos (Real.exp_pos _) hr, ?_, ?_⟩
  · have hlog := (hA.const_mul (-γ)).add (hD.const_mul cK)
    have hlim := (Real.continuous_exp.tendsto (-γ * A + cK * D)).comp hlog
    convert hlim using 1
    funext t
    dsimp [expPrimitive]
    rw [← Real.exp_mul, ← Real.exp_sub]
    congr 1
    dsimp [cK]
    field_simp [hr.ne']
    ring
  · have hlog := hB.neg.add (hD.const_mul cv)
    have hlim := ((Real.continuous_exp.tendsto (-B + cv * D)).comp hlog).div
      (Real.continuous_sqrt.continuousAt.tendsto.comp hsinf) hr.ne'
    convert hlim using 1
    funext t
    dsimp [densityInOrbitTime, expPrimitive]
    rw [div_div]
    have he : t - primitive s t - (-cv * primitive (fun u ↦ Real.sqrt (s u)) t) =
        -(primitive s t - sLim * t) + cv *
          (primitive (fun u ↦ Real.sqrt (s u)) t - Real.sqrt sLim * t) := by
      dsimp [cv]
      field_simp [hr.ne']
      ring
    rw [show Real.exp t / (Real.exp (primitive s t) * Real.sqrt (s t) *
        Real.exp (-cv * primitive (fun u ↦ Real.sqrt (s u)) t)) =
        Real.exp (t - primitive s t - (-cv * primitive (fun u ↦ Real.sqrt (s u)) t)) /
          Real.sqrt (s t) by
      rw [Real.exp_sub, Real.exp_sub]
      field_simp [(Real.sqrt_pos.mpr (hp t)).ne']]
    rw [he]

/-- The limiting exponential amplitudes hold for the genuine physical
energy, density and RN-defined type clock, on the full physical half-line. -/
theorem constructedMass_exponential_amplitudes {γ sLim ULim C : ℝ} {s U : ℝ → ℝ}
    (hs : Continuous s) (hU : Continuous U) (hp : ∀ t, 0 < s t)
    (h₁ : ∀ t ≥ 0, 1 ≤ s t) (hsLim : 1 ≤ sLim)
    (hsinf : Tendsto s atTop (𝓝 sLim))
    (hsbound : ∀ t ≥ 0, |s t - sLim| ≤ C * Real.exp (-2 * t))
    (hUbound : ∀ t ≥ 0, |U t - ULim| ≤ C * Real.exp (-2 * t)) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      Tendsto (fun x ↦ extendedEnergy s U x ^ (-γ) /
        Real.exp (-(γ * ULim / Real.sqrt sLim) * (constructedMass s hs hp h₁).typeClock x))
        atTop (𝓝 a) ∧
      Tendsto (fun x ↦ extendedDensity s x /
        Real.exp (-((sLim - 1) / Real.sqrt sLim) * (constructedMass s hs hp h₁).typeClock x))
        atTop (𝓝 b) := by
  obtain ⟨a, b, ha, hb, hK, hv⟩ := orbit_exponential_amplitudes
    (γ := γ) hs hU hp h₁ hsLim hsinf hsbound hUbound
  refine ⟨a, b, ha, hb, ?_, ?_⟩
  · apply (hK.comp (inverseClock_tendsto_atTop hs hp h₁)).congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    have ht := inverseClock_nonneg hs hp h₁ hx
    have hy := constructedMass_typeClock_at_physicalClock hs hp h₁ ht
    rw [inverseClock_right_inverse hs hp h₁ hx] at hy
    rw [hy, (extended_coordinates_eq (U := U) hs hp hx).2.2.1]
    rfl
  · apply (hv.comp (inverseClock_tendsto_atTop hs hp h₁)).congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    have ht := inverseClock_nonneg hs hp h₁ hx
    have hy := constructedMass_typeClock_at_physicalClock hs hp h₁ ht
    rw [inverseClock_right_inverse hs hp h₁ hx] at hy
    rw [hy, (extended_coordinates_eq (U := U) hs hp hx).2.2.2]
    rfl

/-- The article's half-gamma shape holds for one actual global optimizing
string attached to the named separating graph. Both ratios converge to
positive amplitudes, so in particular both quantities are comparable to
`exp(-2y/√3)` in its actual RN type clock. -/
theorem exists_actual_half_exponential_shape
    (G : krylov.LotkaVolterra.SubcriticalGraph (1 / 2)) :
    ∃ M : Mass, ∃ φ v : ℝ → ℝ, Continuous φ ∧ Continuous v ∧ φ 0 = 1 ∧
      (∀ x ≥ 0, φ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure φ t) ∧
      (∀ L : ℝ≥0, M.typeDensity =ᵐ[volume.restrict (Ioc 0 (L : ℝ))] v) ∧
      M.reward (1 / 2) φ = ENNReal.ofReal (Real.sqrt (G.σ 1)) ∧
      Tendsto M.cumulative atTop (𝓝 (G.σ 1)) ∧
      ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
        Tendsto (fun x ↦ integralEnergy M.measure φ x ^ (-(1 / 2 : ℝ)) /
          Real.exp (-(2 / Real.sqrt 3) * M.typeClock x)) atTop (𝓝 a) ∧
        Tendsto (fun x ↦ v x / Real.exp (-(2 / Real.sqrt 3) * M.typeClock x)) atTop (𝓝 b) := by
  obtain ⟨s, U, hs, hU, hU₀, hpos, hUone, _, hode, hsinf, hUinf, hexp, hcanonical, _⟩ :=
    exists_subcritical_data (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hp : ∀ t, 0 < s t := fun t ↦ zero_lt_one.trans (hpos t).1
  have h₁ : ∀ t ≥ 0, 1 ≤ s t := fun t _ ↦ (hpos t).1.le
  have hUp : ∀ t ≥ 0, 0 < U t := fun t _ ↦ (hpos t).2
  have hd := fun t (_ : 0 < t) ↦ hode t
  obtain ⟨C, _, hbound⟩ := hexp
  norm_num [krylov.LotkaVolterra.saddleS, krylov.LotkaVolterra.saddleU] at hsinf hUinf hbound
  have hsbound : ∀ t ≥ 0, |s t - 3| ≤ C * Real.exp (-2 * t) := by
    intro t ht
    have hh := hbound t ht
    simp only [← neg_mul] at hh
    linarith [abs_nonneg (U t - 4)]
  have hUbound : ∀ t ≥ 0, |U t - 4| ≤ C * Real.exp (-2 * t) := by
    intro t ht
    have hh := hbound t ht
    simp only [← neg_mul] at hh
    linarith [abs_nonneg (s t - 3)]
  obtain ⟨a, b, ha, hb, hK, hv⟩ := constructedMass_exponential_amplitudes
    (γ := (1 / 2 : ℝ)) hs hU hp h₁ (by norm_num : (1 : ℝ) ≤ 3) hsinf hsbound hUbound
  norm_num at hK hv
  have htermLV := krylov.ContinuumControl.orbitValue_tendsto_zero_of_finite_state
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 3) (by norm_num : (0 : ℝ) < 4)
    hsinf hUinf (expPrimitive_tendsto_atTop hU hUone)
  have hterm : Tendsto (physicalOrbitValue (1 / 2) s U) atTop (𝓝 0) :=
    htermLV.comp (inverseClock_tendsto_atTop hs hp h₁)
  obtain ⟨hφ, _, _⟩ := extended_coordinates_continuous hs hU hp h₁
  refine ⟨constructedMass s hs hp h₁, extendedPosition s, extendedDensity s, hφ,
    extendedDensity_continuous hs hp h₁, (extended_initial (U := U) hs hp).1, ?_,
    constructedMass_typeDensity hs hp h₁, ?_, ?_, a, b, ha, hb, ?_, ?_⟩
  · intro x hx
    obtain ⟨hφx, _, _⟩ := constructedMass_state hs hU hp h₁ hU₀ (fun t ht ↦ (hd t ht).2) hx
    rw [hφx]
    congr 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (constructedMass_state hs hU hp h₁ hU₀ (fun t ht ↦ (hd t ht).2) ht.1.le).2.1
  · have hr := constructedMass_reward_allGamma (by norm_num : (1 / 2 : ℝ) ≠ 0)
      hs hU hp h₁ hU₀ hUp hd hterm
    norm_num at hr
    simpa only [hcanonical G] using hr
  · simpa only [hcanonical G] using constructedMass_half_total_mass hs hU hp h₁ hU₀ hd hsinf hUinf
  · apply hK.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [← (constructedMass_state hs hU hp h₁ hU₀ (fun t ht ↦ (hd t ht).2) hx).2.2]
    simp only [neg_mul]
  · simpa only [neg_mul] using hv

end
end krylov.Strings.OptimizerQuadratures
