import polyak.Levels.Geometry.LagEnds
import Mathlib.Analysis.Analytic.Order

/-! Exact analytic quadratic factors of all signed endpoint lags. -/
noncomputable section
namespace polyak.Levels.Geometry
open General Filter
open scoped Topology

theorem analyticAt_endLag_zero (q : Tuning) (s : ℝ) (n : ℤ) :
    AnalyticAt ℝ (endLag q s n) 0 := by
  have hθ : AnalyticAt ℝ (endAngle q s) 0:=analyticAt_endAngle q s (by
    simpa only [shiftNumerator,Real.cos_zero,Real.sin_zero,mul_zero,add_zero] using q.Xi_one_neg.ne)
  exact (Real.analyticAt_cos.comp hθ).sub (Real.analyticAt_cos.comp ((analyticAt_const.mul (analyticAt_id : AnalyticAt ℝ (id : ℝ→ℝ) 0)).sub hθ))

theorem endLag_quadratic_factor (q : Tuning) (s : ℝ) (n : ℤ) :
    ∃U : ℝ→ℝ,AnalyticAt ℝ U 0 ∧
      U 0= -(n:ℝ)*((n:ℝ)+2*tau q)/2 ∧ ∀ω,endLag q s n ω=ω^2*U ω := by
  obtain ⟨F,hF,he⟩:=(analyticAt_endLag_zero q s n).exists_eq_sum_add_pow_mul 3
  let c : ℝ:= -(n:ℝ)*((n:ℝ)+2*tau q)/2
  refine ⟨fun ω=>c+ω*F ω,analyticAt_const.add (analyticAt_id.mul hF),by dsimp only [c]; simp only [zero_mul,add_zero],?_⟩
  intro ω
  have hh:=he ω
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,iteratedDeriv_zero,
    iteratedDeriv_one,endLag_zero,endLag_deriv_zero,smul_eq_mul,mul_zero,add_zero] at hh
  have hsec : iteratedDeriv 2 (endLag q s n) 0= -(n:ℝ)*((n:ℝ)+2*tau q) := by
    simpa only [iteratedDeriv_eq_iterate] using endLag_second_zero q s n
  rw [hsec] at hh
  norm_num only [Nat.factorial_succ,Nat.factorial_zero,Nat.cast_ofNat,mul_one,one_mul] at hh
  dsimp only [c]
  nlinarith [hh]

end polyak.Levels.Geometry
