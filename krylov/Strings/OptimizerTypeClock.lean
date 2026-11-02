import krylov.Strings.OptimizerConstructedMass

/-!
Article: main_krylov, thm:value, type-time admissibility of the global optimizer.
Use: identify its actual RN clock in LV time and prove that it is unbounded;
also identify the exact initial density and right derivative of its mass.
Source: FTC, the actual inverse-clock identity and the positive feedback law.
-/

namespace krylov.Strings.OptimizerQuadratures
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

/-- The constructed density at the initial point is the reciprocal square
root of the shooting coordinate. -/
theorem extendedDensity_initial {s : ℝ → ℝ} (hs : Continuous s)
    (hp : ∀ t, 0 < s t) : extendedDensity s 0 = 1 / Real.sqrt (s 0) := by
  obtain ⟨_, _, _, hv⟩ := extended_coordinates_eq (U := s) hs hp (x := 0) le_rfl
  rw [hv]
  simp [physicalDensity, physicalSlope, physicalPosition, inverseClock_zero hs hp]

/-- The derivative is for the actual global mass, including its distinguished
origin atom; differentiation is from the physical right. -/
theorem constructedMass_right_derivative {s : ℝ → ℝ} (hs : Continuous s)
    (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t) :
    HasDerivWithinAt (constructedMass s hs hp h₁).cumulative
      (s 0)⁻¹ (Ici 0) 0 := by
  have hc := extendedDensity_continuous hs hp h₁
  have hd := ((primitive_derivative (hc.pow 2) 0).const_add 1).hasDerivWithinAt (s := Ici 0)
  have hsq : extendedDensity s 0 ^ 2 = (s 0)⁻¹ := by
    rw [extendedDensity_initial hs hp]
    simp only [one_div, inv_pow, Real.sq_sqrt (hp 0).le]
  simp only [Pi.pow_apply, hsq] at hd
  apply hd.congr
  · intro x hx
    exact OptimizerDensity.globalCumulative_eq _ hc hx
  · exact OptimizerDensity.globalCumulative_eq _ hc le_rfl

/-- The actual RN type clock has the exact orbit-time quadrature `∫√s`.
This verifies the change of clock for the actual global Stieltjes measure. -/
theorem constructedMass_typeClock_at_physicalClock {s : ℝ → ℝ} (hs : Continuous s)
    (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t) {t : ℝ} (ht : 0 ≤ t) :
    (constructedMass s hs hp h₁).typeClock (physicalClock s t) =
      ∫ u in (0 : ℝ)..t, Real.sqrt (s u) := by
  let F : ℝ → ℝ := fun u ↦ primitive (extendedDensity s) (physicalClock s u)
  have hd (u : ℝ) (hu : 0 ≤ u) : HasDerivAt F (Real.sqrt (s u)) u := by
    have hXu : 0 ≤ physicalClock s u := by
      simpa only [physicalClock_zero] using (physicalClock_strictMono hs hp).monotone hu
    have hder := (primitive_derivative (extendedDensity_continuous hs hp h₁)
      (physicalClock s u)).comp u (physicalClock_derivative hs u)
    convert hder using 1
    · rfl
    · obtain ⟨_, _, _, hv⟩ := extended_coordinates_eq (U := s) hs hp hXu
      rw [hv]
      have hinv : inverseClock s (physicalClock s u) = u :=
        Function.leftInverse_invFun (physicalClock_strictMono hs hp).injective u
      simp only [physicalDensity, physicalSlope, physicalPosition, hinv]
      dsimp [physicalSpeed]
      have hroot := Real.sq_sqrt (hp u).le
      field_simp [(expPrimitive_pos s u).ne', (Real.sqrt_pos.mpr (hp u)).ne']
      nlinarith
  have hF : Continuous F := by
    exact (continuous_iff_continuousAt.mpr
      (fun x ↦ (primitive_derivative (extendedDensity_continuous hs hp h₁) x).continuousAt)).comp
      (continuous_iff_continuousAt.mpr (fun u ↦ (physicalClock_derivative hs u).continuousAt))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hF.continuousOn
    (fun u hu ↦ hd u hu.1.le) (hs.sqrt.intervalIntegrable 0 t)
  have hXt : 0 ≤ physicalClock s t := by
    simpa only [physicalClock_zero] using (physicalClock_strictMono hs hp).monotone ht
  rw [constructedMass_typeClock hs hp h₁ hXt]
  simpa only [F, physicalClock_zero, primitive, intervalIntegral.integral_same,
    sub_zero] using hi.symm

/-- The actual type clock dominates the genuine inverse LV clock. -/
theorem constructedMass_typeClock_ge_inverseClock {s : ℝ → ℝ} (hs : Continuous s)
    (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t) {x : ℝ} (hx : 0 ≤ x) :
    inverseClock s x ≤ (constructedMass s hs hp h₁).typeClock x := by
  have ht := inverseClock_nonneg hs hp h₁ hx
  have hid := constructedMass_typeClock_at_physicalClock hs hp h₁ ht
  rw [inverseClock_right_inverse hs hp h₁ hx] at hid
  rw [hid]
  have hi := intervalIntegral.integral_mono_on ht
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ)) volume 0 (inverseClock s x))
    (hs.sqrt.intervalIntegrable 0 (inverseClock s x)) (fun u hu ↦ ?_)
  · simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one,
      inverseClock] using hi
  · exact Real.one_le_sqrt.mpr (by linarith [h₁ u hu.1])

/-- The constructed physical string has an unbounded actual RN type clock.
In particular, its infinite-horizon endpoint reward is not obtained by an
unverified change of variables on a finite type interval. -/
theorem constructedMass_typeClock_tendsto_atTop {s : ℝ → ℝ} (hs : Continuous s)
    (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t) :
    Tendsto (constructedMass s hs hp h₁).typeClock atTop atTop := by
  apply tendsto_atTop_mono' atTop
    ((eventually_ge_atTop (0 : ℝ)).mono (fun x hx ↦
      constructedMass_typeClock_ge_inverseClock hs hp h₁ hx))
  exact inverseClock_tendsto_atTop hs hp h₁

end
end krylov.Strings.OptimizerQuadratures
