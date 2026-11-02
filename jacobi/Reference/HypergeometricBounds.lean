import jacobi.Reference.Hypergeometric
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
Article: jacobi, Lemma C.1.
Uniform coefficient bounds compare the genuine complex 2F1 series with a
positive-parameter community hypergeometric series. They apply also at
terminating parameters and justify analytic dependence without assuming it.
Use: turns the fixed positive reference denominator and the positive majorant factors into genuine real numbers.
-/
namespace jacobi.Reference.Hypergeometric
noncomputable section
open Complex Set Polynomial
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Rising factorial evaluation commutes with the actual real-to-complex inclusion.
Use: turns the fixed positive reference denominator and the positive majorant factors into genuine real numbers.
Article: jacobi, Lemma C.1.
Proof: induction uses the same next-factor recurrence in the two actual coefficient fields. -/
theorem pochhammer_ofReal (s : ℝ) (n : ℕ) :
    (ascPochhammer ℂ n).eval (s:ℂ)=(((ascPochhammer ℝ n).eval s:ℝ):ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval,ascPochhammer_succ_eval,ih]
    push_cast
    rfl

/-- A complex rising factorial is bounded by the positive real rising factorial at any upper bound for its initial norm.
Use: controls all original hypergeometric numerator coefficients uniformly on compact frequency sets.
Article: jacobi, Appendix C.1 (selected endpoint branch).
Proof: each next factor has norm at most the upper parameter plus its
nonnegative integer index. Multiply the positive next-factor bound by
the genuine induction bound. -/
theorem pochhammer_norm_le {u : ℂ} {U : ℝ} (hU : 0<U) (hu : ‖u‖≤U) (n : ℕ) :
    ‖(ascPochhammer ℂ n).eval u‖≤(ascPochhammer ℝ n).eval U := by
  -- The comparison is valid even when a true numerator factor vanishes.
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval,ascPochhammer_succ_eval,norm_mul]
    apply mul_le_mul ih ?_ (norm_nonneg _) (ascPochhammer_pos n U hU).le
    exact (norm_add_le u (n:ℂ)).trans (by rw [Complex.norm_natCast]; linarith)

/-- Genuine complex 2F1 coefficients are dominated by those of a positive-parameter community 2F1 series.
Use: a single convergent series controls the original reference solution on compact frequency sets.
Article: jacobi, Lemma C.1.
Proof: the two numerator Pochhammer norms have the proved positive
bounds. The fixed denominator is the same complex factor for both series,
so even a zero denominator preserves this purely coefficientwise bound. Compare the exact norm product formulas. -/
theorem coefficient_norm_le {u v c : ℂ} {D : ℝ} (hD : 0<D)
    (hu : ‖u‖≤D) (hv : ‖v‖≤D) (n : ℕ) :
    ‖ordinaryHypergeometricCoefficient u v c n‖≤
      ‖ordinaryHypergeometricCoefficient (D:ℂ) (D:ℂ) c n‖ := by
  -- The comparison uses the actual shared denominator, including singular original endpoint weights.
  have hpn := pochhammer_norm_le hD hu n
  have hqn := pochhammer_norm_le hD hv n
  have hreal : ‖(ascPochhammer ℂ n).eval (D:ℂ)‖=(ascPochhammer ℝ n).eval D := by
    rw [pochhammer_ofReal,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (ascPochhammer_pos n D hD)]
  unfold ordinaryHypergeometricCoefficient
  simp only [norm_mul,norm_inv]
  rw [hreal]
  have hpnonneg := (ascPochhammer_pos n D hD).le
  gcongr

/-- The actual community hypergeometric coefficients multiplied by a disk argument are genuinely summable in norm.
Use: provides the true summable majorant for analytic reference parameter dependence.
Article: jacobi, Lemma C.1.
Proof: use the actual community power series sum theorem and the proved unit lower radius bound; norm summability holds strictly inside that ball. -/
theorem summable_norm {u v c x : ℂ} (hx : ‖x‖<1) :
    Summable (fun n => ‖ordinaryHypergeometricCoefficient u v c n*x^n‖) := by
  have hr := (ordinaryHypergeometricSeries ℂ u v c).summable_norm_apply
    (show x∈Metric.eball (0:ℂ) (ordinaryHypergeometricSeries ℂ u v c).radius from by
      apply Metric.eball_subset_eball (radius_ge_one u v c)
      simpa only [Metric.mem_eball,edist_dist,dist_zero_right,ENNReal.ofReal_lt_one] using hx)
  simpa only [ordinaryHypergeometricSeries_apply_eq,smul_eq_mul] using hr

end
end jacobi.Reference.Hypergeometric
