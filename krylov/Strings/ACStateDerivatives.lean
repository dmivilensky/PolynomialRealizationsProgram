import krylov.Strings.StateRegularity
import krylov.ContinuumBV.SingularIdentity

/-!
Article: `main_krylov`, `apC:eq:state`, actual physical derivatives before
the change to the type variable. When the actual singular mass vanishes on
a finite window, its cumulative weighted integrals are genuine primitives
of the measurable Radon--Nikodym density. Lebesgue differentiation then
gives the actual slope and energy derivatives almost everywhere; no
continuity of the density or smoothness of the mass is assumed.
Source: actual Lebesgue decomposition and mathlib's Lebesgue FTC.
-/

namespace krylov.Strings
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

namespace Mass

/-- Actual weighted mass integrals are Lebesgue primitives when the singular
mass of the physical window is zero. -/
theorem cumulativeIntegral_eq_density_integral (M : Mass) (L : ℝ≥0)
    {g : ℝ → ℝ} (hc : Continuous g)
    (hSing : (M.measure.singularPart volume) (Ioc 0 (L : ℝ)) = 0)
    {x : ℝ} (hx : x ∈ Icc 0 (L : ℝ)) :
    (∫ t in Ioc 0 x, g t ∂M.measure) =
      ∫ t in (0 : ℝ)..x, g t * M.typeDensity t ^ 2 := by
  obtain ⟨_, _, heq⟩ := krylov.ContinuumBV.actual_mass_integral_split M
    (M.position_integrable hc x)
  have hz : (M.measure.singularPart volume) (Ioc 0 x) = 0 :=
    measure_mono_null (Ioc_subset_Ioc_right hx.2) hSing
  rw [setIntegral_measure_zero _ hz, add_zero] at heq
  rw [intervalIntegral.integral_of_le hx.1]
  simpa only [mul_comm] using heq

/-- The actual density-weighted continuous mass costs are locally integrable,
including for merely measurable physical density. -/
theorem density_mul_intervalIntegrable (M : Mass) (L : ℝ≥0)
    {g : ℝ → ℝ} (hc : Continuous g) :
    IntervalIntegrable (fun t ↦ g t * M.typeDensity t ^ 2) volume 0 (L : ℝ) := by
  have hL : (0 : ℝ) ≤ (L : ℝ) := L.property
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hL).2
  have hi := (krylov.ContinuumBV.actual_mass_integral_split M
    (M.position_integrable hc (L : ℝ))).1
  simpa only [mul_comm] using hi

/-- Lebesgue differentiation applies to the genuine cumulative Stieltjes
integral once its actual singular mass vanishes on the window. -/
theorem cumulativeIntegral_ae_hasDerivAt_of_singular_zero (M : Mass) (L : ℝ≥0)
    {g : ℝ → ℝ} (hc : Continuous g)
    (hSing : (M.measure.singularPart volume) (Ioc 0 (L : ℝ)) = 0) :
    ∀ᵐ x : ℝ, x ∈ Ioo 0 (L : ℝ) →
      HasDerivAt (fun z ↦ ∫ t in Ioc 0 z, g t ∂M.measure)
        (g x * M.typeDensity x ^ 2) x := by
  have hi := density_mul_intervalIntegrable M L hc
  filter_upwards [hi.ae_hasDerivAt_integral] with x hx
  intro hxin
  have hxclosed : x ∈ uIcc 0 (L : ℝ) := by
    have hL : (0 : ℝ) ≤ (L : ℝ) := L.property
    rw [uIcc_of_le hL]
    exact ⟨hxin.1.le, hxin.2.le⟩
  have hd := hx hxclosed 0 left_mem_uIcc
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hxin.1 hxin.2] with t ht
  exact cumulativeIntegral_eq_density_integral M L hc hSing ⟨ht.1.le, ht.2.le⟩

/-- Both actual physical state derivatives follow from the same genuine
mass decomposition. Position continuity suffices; no state equation or
optimality hypothesis is used in this measure-theoretic step. -/
theorem slope_energy_ae_hasDerivAt (M : Mass) (L : ℝ≥0) {φ : ℝ → ℝ}
    (hc : Continuous φ)
    (hSing : (M.measure.singularPart volume) (Ioc 0 (L : ℝ)) = 0) :
    ∀ᵐ x : ℝ, x ∈ Ioo 0 (L : ℝ) →
      HasDerivAt (integralSlope M.measure φ) (φ x * M.typeDensity x ^ 2) x ∧
        HasDerivAt (integralEnergy M.measure φ) (φ x ^ 2 * M.typeDensity x ^ 2) x := by
  filter_upwards [cumulativeIntegral_ae_hasDerivAt_of_singular_zero M L hc hSing,
    cumulativeIntegral_ae_hasDerivAt_of_singular_zero M L (hc.pow 2) hSing] with x hp hK
  intro hx
  exact ⟨(hp hx).const_add 1, (hK hx).const_add 1⟩

end Mass
end
end krylov.Strings
