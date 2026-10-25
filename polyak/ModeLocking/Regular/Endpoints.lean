import polyak.ModeLocking.Regular.Slackness

/-! The jets at zero of the same analytic extension used in regularity. -/
noncomputable section
namespace polyak.ModeLocking
open General Levels Filter
open scoped BigOperators Topology

theorem lagExtension_eventually_endLag (q : Tuning) (s : ℝ) (n : ℤ) :
    lagExtension q s n =ᶠ[𝓝 0] Geometry.endLag q s n := by
  have hn : Geometry.shiftNumerator q s 0 < 0 := by
    simpa only [Geometry.shiftNumerator, Real.cos_zero, Real.sin_zero, mul_zero, add_zero]
      using q.Xi_one_neg
  filter_upwards [(Geometry.analyticAt_shiftNumerator q s 0).continuousAt.eventually
    (eventually_lt_nhds hn)] with x hx
  unfold lagExtension Geometry.extendedLag Geometry.jointAngle
  dsimp only
  rw [Chart.rawToCoefficient_actual]
  have hnum : Geometry.ambientNumerator
      ![(Chart.coefficients q).c0, (Chart.coefficients q).c1, (Chart.coefficients q).c2, s, x] =
      Geometry.shiftNumerator q s x := Geometry.ambientNumerator_coefficientPoint q s x
  rw [Geometry.ambientAngle_eq_end_of_neg (by rw [hnum]; exact hx)]
  unfold Geometry.ambientEndAngle
  rw [hnum]
  rfl

theorem lagExtension_deriv_zero (q : Tuning) (s : ℝ) (n : ℤ) :
    deriv (lagExtension q s n) 0 = 0 := by
  rw [(lagExtension_eventually_endLag q s n).deriv_eq, Geometry.endLag_deriv_zero]

theorem lagExtension_second_zero (q : Tuning) (s : ℝ) (n : ℤ) :
    deriv^[2] (lagExtension q s n) 0 = -(n : ℝ) * ((n : ℝ) + 2 * Geometry.tau q) := by
  change deriv (deriv (lagExtension q s n)) 0 = _
  rw [(lagExtension_eventually_endLag q s n).deriv.deriv_eq]
  exact Geometry.endLag_second_zero q s n

theorem finiteSymbol_deriv_zero (q : Tuning) (s : ℝ) (N : Finset ℤ) (a : ℤ → ℝ) :
    deriv (finiteSymbol q s N a) 0 = 0 := by
  unfold finiteSymbol
  rw [deriv_fun_sum (fun n _ => (analyticAt_lagExtension q s n ⟨le_rfl, Real.pi_pos.le⟩).differentiableAt.const_mul (a n))]
  simp only [deriv_const_mul_field, lagExtension_deriv_zero, mul_zero, Finset.sum_const_zero]

theorem finiteSymbol_second_zero (q : Tuning) (s : ℝ) (N : Finset ℤ) (a : ℤ → ℝ) :
    deriv^[2] (finiteSymbol q s N a) 0 =
      -(∑ n ∈ N, a n * (n : ℝ) * ((n : ℝ) + 2 * Geometry.tau q)) := by
  have he : deriv (finiteSymbol q s N a) =ᶠ[𝓝 0]
      fun x => ∑ n ∈ N, a n * deriv (lagExtension q s n) x := by
    have hall : ∀ n ∈ N, ∀ᶠ x in 𝓝 0, AnalyticAt ℝ (lagExtension q s n) x :=
      fun n _ => (analyticAt_lagExtension q s n ⟨le_rfl, Real.pi_pos.le⟩).eventually_analyticAt
    rw [← Filter.eventually_all_finset] at hall
    filter_upwards [hall] with x hx
    unfold finiteSymbol
    rw [deriv_fun_sum (fun n hn => (hx n hn).differentiableAt.const_mul (a n))]
    simp only [deriv_const_mul_field]
  change deriv (deriv (finiteSymbol q s N a)) 0 = _
  rw [he.deriv_eq, deriv_fun_sum (fun n _ =>
    (analyticAt_lagExtension q s n ⟨le_rfl, Real.pi_pos.le⟩).deriv.differentiableAt.const_mul (a n))]
  simp only [deriv_const_mul_field, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n _
  change a n * deriv^[2] (lagExtension q s n) 0 = _
  rw [lagExtension_second_zero]
  ring

namespace RegularData
variable {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L)

theorem symbol_slope_zero : deriv (finiteSymbol q s D.lags D.dual) 0 = 0 :=
  finiteSymbol_deriv_zero q s D.lags D.dual

theorem symbol_curvature_zero : deriv^[2] (finiteSymbol q s D.lags D.dual) 0 < 0 := by
  rw [finiteSymbol_second_zero]
  exact neg_neg_of_pos D.endpoint_curvature

end RegularData
end polyak.ModeLocking
