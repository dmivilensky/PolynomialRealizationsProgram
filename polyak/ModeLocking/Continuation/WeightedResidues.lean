import polyak.ModeLocking.Continuation.LiftedWeights

/-! Value and slope identities on the fixed grid for arbitrary new weights
and arbitrary tunings. The residue partition is the original finite one. -/
noncomputable section
namespace polyak.ModeLocking.RegularData
open General Levels
open scoped BigOperators
variable {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L)

theorem weighted_symbol_grid (q' : Tuning) (t : ℝ) (a : ℤ → ℝ)
    (ω : Frequency) (hω : ω ∈ periodicGrid L) :
    finiteSymbol q' t D.lags a ω =
      ∑ r, Continuation.classSum (D.lagClass r) a * (Geometry.shiftedCurve q' t).lag (D.reps r) ω := by
  classical
  rw [finiteSymbol_actual, D.sum_classes]
  have hz : (∑ n ∈ D.lags, if n % (L : ℤ) = 0 then a n * (Geometry.shiftedCurve q' t).lag n ω else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro n _
    split_ifs with hn
    · rw [lag_mod_grid (Geometry.shiftedCurve q' t) hω n, hn, Curve.lag_zero, mul_zero]
    · rfl
  rw [hz, add_zero]
  apply Finset.sum_congr rfl
  intro r _
  simp only [Continuation.classSum, lagClass, Finset.sum_filter, Finset.sum_mul, ite_mul, zero_mul]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : n % (L : ℤ) = D.reps r
  · rw [ite_eq_left hn, ite_eq_left hn, lag_mod_grid (Geometry.shiftedCurve q' t) hω n, hn]
  · rw [ite_eq_right hn, ite_eq_right hn]

theorem weighted_slope_grid (q' : Tuning) (t : ℝ) (a : ℤ → ℝ) (i : Fin D.d) :
    deriv (finiteSymbol q' t D.lags a) (D.atoms i : ℝ) =
      (∑ r, Continuation.classSum (D.lagClass r) a * deriv (lagExtension q' t (D.reps r)) (D.atoms i)) +
      (∑ r, (L : ℝ) * Real.sin ((D.reps r : ℝ) * (D.atoms i : ℝ) - Geometry.shiftedCurve q' t (D.atoms i)) *
        Continuation.classMoment (D.lagClass r) (fun n => ((n / (L : ℤ) : ℤ) : ℝ)) a) +
      ∑ n ∈ D.lags, if n % (L : ℤ) = 0 then a n * deriv (lagExtension q' t n) (D.atoms i) else 0 := by
  classical
  have he : deriv (finiteSymbol q' t D.lags a) (D.atoms i : ℝ) =
      ∑ n ∈ D.lags, a n * deriv (lagExtension q' t n) (D.atoms i) := by
    unfold finiteSymbol
    rw [deriv_fun_sum (fun n _ => (analyticAt_lagExtension q' t n (D.atoms i).property).differentiableAt.const_mul _)]
    simp only [deriv_const_mul_field]
  rw [he, D.sum_classes]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  simp only [Continuation.classSum, Continuation.classMoment, lagClass,
    Finset.sum_filter, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : n % (L : ℤ) = D.reps r
  · rw [ite_eq_left hn, Continuation.slope_mod_grid q' t (D.atoms i) (D.atoms_grid i) n, hn]
    simp only [ite_true]
    ring
  · simp only [ite_eq_right hn, zero_mul, mul_zero, add_zero]

theorem lifted_symbol_grid (q' : Tuning) (t : ℝ) (μ m : Fin D.d → ℝ)
    (ω : Frequency) (hω : ω ∈ periodicGrid L) :
    finiteSymbol q' t D.lags (D.liftedWeights μ m) ω =
      ∑ r, μ r * (Geometry.shiftedCurve q' t).lag (D.reps r) ω := by
  rw [D.weighted_symbol_grid q' t (D.liftedWeights μ m) ω hω]
  simp only [D.liftedWeights_classSum]

theorem lifted_slope_grid (q' : Tuning) (t : ℝ) (μ m : Fin D.d → ℝ) (i : Fin D.d) :
    deriv (finiteSymbol q' t D.lags (D.liftedWeights μ m)) (D.atoms i : ℝ) =
      (∑ r, μ r * deriv (lagExtension q' t (D.reps r)) (D.atoms i)) +
      (∑ r, (L : ℝ) * Real.sin ((D.reps r : ℝ) * (D.atoms i : ℝ) - Geometry.shiftedCurve q' t (D.atoms i)) * m r) +
      ∑ n ∈ D.lags, if n % (L : ℤ) = 0 then D.dual n * deriv (lagExtension q' t n) (D.atoms i) else 0 := by
  rw [D.weighted_slope_grid q' t (D.liftedWeights μ m) i]
  simp only [D.liftedWeights_classSum, D.liftedWeights_classMoment]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : n % (L : ℤ) = 0
  · rw [ite_eq_left hn, ite_eq_left hn, D.liftedWeights_zeroClass μ m hn]
  · rw [ite_eq_right hn, ite_eq_right hn]

end polyak.ModeLocking.RegularData
