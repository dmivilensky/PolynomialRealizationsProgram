import krylov.Strings.OptimizerDensityMass

/-!
Article: main_krylov, thm:value, the infinite physical feedback string.
Use: realize a continuous density by a genuine mass on the entire half-line,
without bounded total mass, and identify its RN clock on every finite window.
Source: the Stieltjes measure of the primitive of the squared density. Compact
measure/RN identifications are reused from OptimizerDensityMass.
-/

namespace krylov.Strings.OptimizerDensity
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

/-- The distinguished unit atom followed by a continuous density on [0,∞). -/
def globalCumulative (v : ℝ → ℝ) (hc : Continuous v) : StieltjesFunction ℝ where
  toFun x := if x < 0 then 0 else 1 + ∫ t in (0 : ℝ)..x, v t ^ 2
  mono' := by
    intro x y hxy
    by_cases hx : x < 0
    · by_cases hy : y < 0
      · simp only [ite_eq_left hx, ite_eq_left hy, le_refl]
      · simp only [ite_eq_left hx, ite_eq_right hy]
        have hi : 0 ≤ ∫ t in (0 : ℝ)..y, v t ^ 2 :=
          intervalIntegral.integral_nonneg (not_lt.mp hy) (fun t _ ↦ sq_nonneg (v t))
        linarith
    · have hy : ¬y < 0 := not_lt.mpr ((not_lt.mp hx).trans hxy)
      simp only [ite_eq_right hx, ite_eq_right hy]
      apply add_le_add_right
      exact intervalIntegral.integral_mono_interval le_rfl (not_lt.mp hx) hxy
        (Eventually.of_forall (fun t ↦ sq_nonneg (v t))) ((hc.pow 2).intervalIntegrable 0 y)
  right_continuous' := by
    intro x
    by_cases hx : x < 0
    · apply (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq
      · filter_upwards [eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hx)] with y hy
        exact ite_eq_left hy
      · exact ite_eq_left hx
    · have hd := ((hc.pow 2).integral_hasStrictDerivAt 0 x).hasDerivAt.const_add 1
      apply hd.continuousAt.continuousWithinAt.congr
      · intro y hy
        exact ite_eq_right (not_lt.mpr ((not_lt.mp hx).trans hy))
      · exact ite_eq_right hx

/-- An actual infinite string, allowing infinite total mass. -/
def globalMass (v : ℝ → ℝ) (hc : Continuous v) : Mass where
  cumulative := globalCumulative v hc
  origin := by simp [globalCumulative]
  negative := by intro x hx; exact ite_eq_left hx

theorem globalCumulative_eq (v : ℝ → ℝ) (hc : Continuous v) {x : ℝ} (hx : 0 ≤ x) :
    (globalMass v hc).cumulative x = 1 + ∫ t in (0 : ℝ)..x, v t ^ 2 :=
  ite_eq_right (not_lt.mpr hx)

/-- The global mass agrees exactly with every already constructed compact
representative. This transports all compact RN results without duplicating them. -/
theorem globalMass_restrict_compact (v : ℝ → ℝ) (hc : Continuous v) (L : ℝ≥0) :
    (globalMass v hc).measure.restrict (Ioc 0 (L : ℝ)) =
      (mass v hc L).measure.restrict (Ioc 0 (L : ℝ)) := by
  apply LocalMass.measure_restrict_eq_of_cumulative_eq
  intro x hx
  rw [globalCumulative_eq v hc hx.1, cumulative_eq v hc L hx]

theorem globalMass_restrict_density (v : ℝ → ℝ) (hc : Continuous v) (L : ℝ≥0) :
    (globalMass v hc).measure.restrict (Ioc 0 (L : ℝ)) =
      (krylov.ContinuumControl.densityMass v).restrict (Ioc 0 (L : ℝ)) :=
  (globalMass_restrict_compact v hc L).trans (measure_restrict_eq v hc L)

/-- Actual RN type density of the global string, on any finite window. -/
theorem global_typeDensity_eq_abs_ae (v : ℝ → ℝ) (hc : Continuous v) (L : ℝ≥0) :
    (globalMass v hc).typeDensity =ᵐ[volume.restrict (Ioc 0 (L : ℝ))] fun x ↦ |v x| :=
  ((globalMass v hc).typeDensity_eq_ae_of_restrict_eq (mass v hc L)
    (globalMass_restrict_compact v hc L)).trans (typeDensity_eq_abs_ae v hc L)

/-- The global actual type clock is the printed physical density primitive. -/
theorem global_typeClock_eq_integral (v : ℝ → ℝ) (hc : Continuous v)
    (hv : ∀ x ≥ 0, 0 ≤ v x) {x : ℝ} (hx : 0 ≤ x) :
    (globalMass v hc).typeClock x = ∫ t in (0 : ℝ)..x, v t := by
  let L : ℝ≥0 := ⟨x, hx⟩
  rw [(globalMass v hc).typeClock_eq_of_restrict_eq (mass v hc L)
    (globalMass_restrict_compact v hc L) hx le_rfl]
  exact typeClock_eq_integral v hc L (fun t ht ↦ hv t ht.1) ⟨hx, le_rfl⟩

end
end krylov.Strings.OptimizerDensity
