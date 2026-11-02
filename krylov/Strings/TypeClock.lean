import krylov.Strings.TypeDensity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
Article: main_krylov, s3:def:string, y(x)=integral_0^x varsigma.
Use: construct the actual type clock and prove its local integrability and
absolute continuity from the genuine mass decomposition.
Source: mathlib Radon–Nikodym integrability and absolute continuity of integrals.
-/

namespace krylov.Strings
noncomputable section
open Set MeasureTheory

namespace Mass

/-- The type density is integrable on every finite physical window,
even when most or all of the mass is singular. -/
theorem typeDensity_integrableOn (M : Mass) (a b : ℝ) :
    IntegrableOn M.typeDensity (Ioc a b) volume := by
  have hi : IntegrableOn (fun x ↦ (M.measure.rnDeriv volume x).toReal)
      (Ioc a b) volume := Measure.integrableOn_toReal_rnDeriv (M.measure_Ioc_lt_top a b).ne
  have hconst : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Ioc a b) volume :=
    integrableOn_const (by simp [Real.volume_Ioc])
  apply (hconst.add hi).mono' M.measurable_typeDensity.aestronglyMeasurable.restrict
  filter_upwards with x
  rw [Real.norm_of_nonneg (M.typeDensity_nonneg x)]
  have ht := Real.sq_sqrt (ENNReal.toReal_nonneg : 0 ≤ (M.measure.rnDeriv volume x).toReal)
  have hn := M.typeDensity_nonneg x
  dsimp [typeDensity] at hn ⊢
  nlinarith [sq_nonneg (Real.sqrt (M.measure.rnDeriv volume x).toReal - 1)]

/-- The physical type clock, with the article's zero initial type. -/
def typeClock (M : Mass) (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, M.typeDensity t

/-- The type clock is normalized at the distinguished initial atom. -/
@[simp] theorem typeClock_zero (M : Mass) : M.typeClock 0 = 0 := by
  simp [typeClock]

/-- No negative type is collected on a positive physical interval. -/
theorem typeClock_nonneg (M : Mass) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ M.typeClock x :=
  intervalIntegral.integral_nonneg hx (fun t _ ↦ M.typeDensity_nonneg t)

/-- The clock has the exact half-open integral convention used in the
string equations; the Lebesgue-null origin contributes no type. -/
theorem typeClock_eq_integral (M : Mass) {x : ℝ} (hx : 0 ≤ x) :
    M.typeClock x = ∫ t in Ioc 0 x, M.typeDensity t :=
  intervalIntegral.integral_of_le hx

/-- Absolute continuity is proved for the actual type clock, not imposed
as an extra assumption excluding singular mass. -/
theorem typeClock_absolutelyContinuousOnInterval (M : Mass) {b : ℝ} (hb : 0 ≤ b) :
    AbsolutelyContinuousOnInterval M.typeClock 0 b := by
  have hi : IntervalIntegrable M.typeDensity volume 0 b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb]
    exact M.typeDensity_integrableOn 0 b
  exact hi.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc

end Mass
end
end krylov.Strings
