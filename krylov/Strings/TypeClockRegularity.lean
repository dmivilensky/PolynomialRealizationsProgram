import krylov.Strings.TypeClockInverse
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
Article: main_krylov, apC:eq:reduced.
Use: derivative and strict monotonicity of the genuine RN-defined clock.
Positivity is only almost everywhere; no density continuity or lower bound
is imposed.
Source: Lebesgue differentiation and positivity of a Lebesgue integral.
-/

namespace krylov.Strings
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

namespace Mass

/-- Integrability of the actual type density on every oriented interval. -/
theorem typeDensity_intervalIntegrable (M : Mass) (a b : ℝ) :
    IntervalIntegrable M.typeDensity volume a b := by
  rw [intervalIntegrable_iff]
  exact M.typeDensity_integrableOn (min a b) (max a b)

/-- The actual type clock differentiates to its RN density almost everywhere. -/
theorem typeClock_ae_hasDerivAt (M : Mass) (L : ℝ≥0) :
    ∀ᵐ x : ℝ, x ∈ Ioo 0 (L : ℝ) → HasDerivAt M.typeClock (M.typeDensity x) x := by
  filter_upwards [(M.typeDensity_intervalIntegrable 0 L).ae_hasDerivAt_integral] with x hx hxin
  exact hx (uIcc_of_le L.property ▸ Ioo_subset_Icc_self hxin) 0 left_mem_uIcc

/-- Continuity of the actual type clock on its entire physical line. -/
theorem typeClock_continuous (M : Mass) : Continuous M.typeClock :=
  intervalIntegral.continuous_primitive (M.typeDensity_intervalIntegrable) 0

/-- The exact clock increment is the integral of the genuine density. -/
theorem typeClock_sub (M : Mass) (a b : ℝ) :
    M.typeClock b - M.typeClock a = ∫ x in a..b, M.typeDensity x :=
  intervalIntegral.integral_interval_sub_left
    (M.typeDensity_intervalIntegrable 0 b) (M.typeDensity_intervalIntegrable 0 a)

/-- Positive density almost everywhere makes the actual type clock strictly
increasing on the physical window, even when the density approaches zero. -/
theorem typeClock_strictMonoOn (M : Mass) (L : ℝ≥0)
    (hp : ∀ᵐ x : ℝ, x ∈ Ioo 0 (L : ℝ) → 0 < M.typeDensity x) :
    StrictMonoOn M.typeClock (Icc 0 (L : ℝ)) := by
  intro a ha b hb hab
  rw [← sub_pos, M.typeClock_sub]
  have hi := M.typeDensity_integrableOn a b
  have hn : 0 ≤ᵐ[volume.restrict (Ioc a b)] M.typeDensity :=
    Eventually.of_forall (M.typeDensity_nonneg ·)
  have hp' : ∀ᵐ x ∂volume.restrict (Ioc a b), 0 < M.typeDensity x := by
    apply ae_restrict_of_ae_eq_of_ae_restrict Ioo_ae_eq_Ioc
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hp] with x hx hxin
    exact hx ⟨ha.1.trans_lt hxin.1, hxin.2.trans_le hb.2⟩
  rw [intervalIntegral.integral_of_le hab.le]
  apply lt_of_le_of_ne (integral_nonneg_of_ae hn)
  intro he
  have hz := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp he.symm
  have hfalse : ∀ᵐ x ∂volume.restrict (Ioc a b), False := by
    filter_upwards [hp', hz] with x hx hxz
    exact hx.ne' hxz
  have hempty : volume (Ioc a b) = 0 := by
    simpa using (ae_iff.mp hfalse)
  simp [Real.volume_Ioc, ENNReal.ofReal_eq_zero, not_le.mpr (sub_pos.mpr hab)] at hempty

end Mass
end
end krylov.Strings
