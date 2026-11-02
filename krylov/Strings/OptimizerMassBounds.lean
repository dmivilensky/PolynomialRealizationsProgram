import krylov.Strings.OptimizerMassShape

/-!
Article: main_krylov, thm:value, finiteness of optimizer mass.
Use: dominate the actual LV-time mass density by an integrable exponential,
then obtain a finite limit for the genuine physical cumulative mass.
Source: the strict lower stable corridor and elementary exponential FTC.
-/

namespace krylov.Strings.OptimizerQuadratures
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

/-- A constant lower rate bound gives the corresponding linear primitive bound. -/
theorem primitive_ge_const_mul {s : ℝ → ℝ} (hs : Continuous s) {c t : ℝ}
    (hc : ∀ u ≥ 0, c ≤ s u) (ht : 0 ≤ t) : c * t ≤ primitive s t := by
  have hi := intervalIntegral.integral_mono_on ht
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ c) volume 0 t)
    (hs.intervalIntegrable 0 t) (fun u hu ↦ hc u hu.1)
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm, primitive] using hi

/-- The feedback mass rate has the exponential majorant when the state stays above one plus gamma. -/
theorem orbit_mass_rate_le_exp {γ : ℝ} {s : ℝ → ℝ} (hs : Continuous s)
    (hlower : ∀ u ≥ 0, 1 + γ ≤ s u) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp t / expPrimitive s t ≤ Real.exp (-γ * t) := by
  rw [expPrimitive, ← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  linarith [primitive_ge_const_mul hs hlower ht]

/-- Actual mass in LV time is the unit origin atom plus the integrated mass rate. -/
theorem orbitMass_eq_integral {s : ℝ → ℝ} (hs : Continuous s)
    (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t) {t : ℝ} (ht : 0 ≤ t) :
    orbitMass s t = 1 + ∫ u in (0 : ℝ)..t, Real.exp u / expPrimitive s u := by
  have hc := Real.continuous_exp.div (expPrimitive_continuous hs)
    (fun u ↦ (expPrimitive_pos s u).ne')
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht
    (orbitMass_continuous hs hp h₁).continuousOn
    (fun u hu ↦ orbitMass_derivative hs hp h₁ hu.1.le) (hc.intervalIntegrable 0 t)
  rw [orbitMass_zero] at hi
  linarith

/-- The exact finite integral of the decaying exponential mass majorant. -/
theorem integral_exp_neg_mul {γ t : ℝ} (hγ : 0 < γ) (ht : 0 ≤ t) :
    ∫ u in (0 : ℝ)..t, Real.exp (-γ * u) = (1 - Real.exp (-γ * t)) / γ := by
  have hd (u : ℝ) : HasDerivAt (fun u ↦ Real.exp (-γ * u) / (-γ))
      (Real.exp (-γ * u)) u := by
    convert (((hasDerivAt_id u).const_mul (-γ)).exp).div_const (-γ) using 1
    · rfl
    · simp [hγ.ne']
  have hc : Continuous (fun u ↦ Real.exp (-γ * u)) := by fun_prop
  have hcont : Continuous (fun u ↦ Real.exp (-γ * u) / (-γ)) := by fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hcont.continuousOn
    (fun u _ ↦ hd u) (hc.intervalIntegrable 0 t)
  rw [hi]
  simp only [mul_zero, Real.exp_zero]
  ring

/-- A concrete finite bound, uniform over the constructed stable orbit. -/
theorem orbitMass_le {γ : ℝ} (hγ : 0 < γ) {s : ℝ → ℝ} (hs : Continuous s)
    (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t)
    (hlower : ∀ u ≥ 0, 1 + γ ≤ s u) {t : ℝ} (ht : 0 ≤ t) :
    orbitMass s t ≤ 1 + 1 / γ := by
  have hc := Real.continuous_exp.div (expPrimitive_continuous hs)
    (fun u ↦ (expPrimitive_pos s u).ne')
  have he : Continuous (fun u : ℝ ↦ Real.exp (-γ * u)) := by fun_prop
  have hm := intervalIntegral.integral_mono_on (μ := volume) ht (hc.intervalIntegrable 0 t)
    (he.intervalIntegrable 0 t) (fun u hu ↦ orbit_mass_rate_le_exp hs hlower hu.1)
  rw [orbitMass_eq_integral hs hp h₁ ht]
  rw [integral_exp_neg_mul hγ ht] at hm
  have hb : (1 - Real.exp (-γ * t)) / γ ≤ 1 / γ :=
    div_le_div_of_nonneg_right (by linarith [Real.exp_pos (-γ * t)]) hγ.le
  exact add_le_add le_rfl (hm.trans hb)

/-- The constructed cumulative mass satisfies its global bound, including the origin atom. -/
theorem constructedMass_cumulative_le {γ : ℝ} (hγ : 0 < γ) {s : ℝ → ℝ}
    (hs : Continuous s) (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t)
    (hlower : ∀ u ≥ 0, 1 + γ ≤ s u) (x : ℝ) :
    (constructedMass s hs hp h₁).cumulative x ≤ 1 + 1 / γ := by
  by_cases hx : 0 ≤ x
  · have ht := inverseClock_nonneg hs hp h₁ hx
    have hm := constructedMass_cumulative_at_physicalClock hs hp h₁ ht
    rw [inverseClock_right_inverse hs hp h₁ hx] at hm
    rw [hm]
    exact orbitMass_le hγ hs hp h₁ hlower ht
  · rw [(constructedMass s hs hp h₁).negative x (not_le.mp hx)]
    positivity

/-- Actual optimizer mass is finite for every strictly positive subcritical
gamma. No total-mass hypothesis was needed in constructing the global mass. -/
theorem constructedMass_finite_limit {γ : ℝ} (hγ : 0 < γ) {s : ℝ → ℝ}
    (hs : Continuous s) (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t)
    (hlower : ∀ u ≥ 0, 1 + γ ≤ s u) :
    ∃ m : ℝ, 1 ≤ m ∧ m ≤ 1 + 1 / γ ∧
      Tendsto (constructedMass s hs hp h₁).cumulative atTop (𝓝 m) := by
  let M := constructedMass s hs hp h₁
  have hb : BddAbove (range M.cumulative) :=
    ⟨1 + 1 / γ, by rintro _ ⟨x, rfl⟩; exact constructedMass_cumulative_le hγ hs hp h₁ hlower x⟩
  refine ⟨⨆ x, M.cumulative x, ?_, ?_, tendsto_atTop_ciSup M.cumulative.mono hb⟩
  · simpa only [M.origin] using le_ciSup hb (0 : ℝ)
  · exact ciSup_le (fun x ↦ constructedMass_cumulative_le hγ hs hp h₁ hlower x)

end
end krylov.Strings.OptimizerQuadratures
