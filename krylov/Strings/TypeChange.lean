import krylov.Strings.TypeReduced

/-!
Article: main_krylov, apC:eq:reduced.
Use: the actual type-coordinate theorem for every admissible absolutely
continuous string with merely measurable positive density. Compact windows
are arbitrary, so the theorem applies locally on finite and infinite
physical strings alike.
Source: the actual RN clock, its inverse and `actual_reduced_ae`.
-/

namespace krylov.Strings.TypeChange
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

/-- A.e. positive physical density gives a.e. positive type-time control.
State positivity follows from the original Volterra equation alone. -/
theorem actual_control_positive_ae (M : Mass) (L : ℝ≥0) (hL : 0 < L) {φ : ℝ → ℝ}
    (hc : Continuous φ)
    (he : ∀ x ∈ Icc 0 (L : ℝ),
      φ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure φ t)
    (hv : ∀ᵐ x : ℝ, x ∈ Ioo 0 (L : ℝ) → 0 < M.typeDensity x) :
    ∀ᵐ y : ℝ, y ∈ Ioo 0 (M.typeClock L) →
      0 < control φ (integralSlope M.measure φ) M.typeDensity
        (inverse M.typeClock 0 L) y := by
  have hm := M.typeClock_strictMonoOn L hv
  have htransfer := ae_transfer (Y := M.typeClock) (v := M.typeDensity)
    (show (0 : ℝ) < (L : ℝ) from hL) hm (M.typeDensity_intervalIntegrable 0 L)
    (fun x _ ↦ M.typeDensity_nonneg x) (M.typeClock_sub 0 L)
    (M.typeClock_ae_hasDerivAt L) hv
  filter_upwards [htransfer] with y hy hyt
  have hy' : y ∈ Ioo (M.typeClock 0) (M.typeClock L) := by simpa using hyt
  have hx := inverse_mem_interior L.property M.typeClock_continuous.continuousOn hm hy'
  obtain ⟨hφ, hp, _⟩ := actual_state_positive M L hc he _ (Ioo_subset_Icc_self hx)
  exact div_pos hp (mul_pos (hy hy') hφ)

/-- Complete change to the actual type variable: an actual inverse exists,
is continuous, has both exact inverse identities, and satisfies all four
printed reduced equations with positive control a.e. in type. Admissibility
is only the continuous original Volterra state; AC mass and positive density
are local measure assumptions, with no smooth density hypothesis. -/
theorem actual_type_change (M : Mass) (L : ℝ≥0) (hL : 0 < L) {φ : ℝ → ℝ}
    (hc : Continuous φ)
    (he : ∀ x ∈ Icc 0 (L : ℝ),
      φ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure φ t)
    (hSing : (M.measure.singularPart volume) (Ioc 0 (L : ℝ)) = 0)
    (hv : ∀ᵐ x : ℝ, x ∈ Ioo 0 (L : ℝ) → 0 < M.typeDensity x) :
    ∃ X : ℝ → ℝ,
      (∀ x ∈ Icc 0 (L : ℝ), X (M.typeClock x) = x) ∧
      (∀ y ∈ Icc 0 (M.typeClock L), M.typeClock (X y) = y) ∧
      ContinuousOn X (Ioo 0 (M.typeClock L)) ∧
      ∀ᵐ y : ℝ, y ∈ Ioo 0 (M.typeClock L) →
        0 < control φ (integralSlope M.measure φ) M.typeDensity X y ∧
        ReducedAt φ (integralSlope M.measure φ) (integralEnergy M.measure φ)
          M.typeDensity X y := by
  have hm := M.typeClock_strictMonoOn L hv
  refine ⟨inverse M.typeClock 0 L, fun _ hx ↦ inverse_clock hm hx, ?_, ?_, ?_⟩
  · intro y hy
    exact clock_inverse L.property M.typeClock_continuous.continuousOn (by simpa using hy)
  · intro y hy
    apply (inverse_continuousAt L.property M.typeClock_continuous.continuousOn hm
      (by simpa using hy)).continuousWithinAt
  · filter_upwards [actual_control_positive_ae M L hL hc he hv,
      actual_reduced_ae M L hL hc he hSing hv] with y hp hd hy
    exact ⟨hp hy, hd hy⟩

end
end krylov.Strings.TypeChange
