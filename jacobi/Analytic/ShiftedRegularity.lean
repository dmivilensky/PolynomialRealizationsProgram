import jacobi.Analytic.ShiftedMassFormula
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
Article: jacobi, Appendix E.1.
The actual shifted mass and second moment are real analytic throughout
the full real-shift interval above the first pole. Their original
convergent series are already identified with the genuine normalized
Bessel quotient and its derivative, so no regularity certificate is
introduced. This shift regularity is separate from the still required
complex continuation in the Bessel order alpha in Theorem 4.2.
Use: shiftedMass_analytic applies the actual adjacent-order quotient formula on its full real shifted domain, including zero and negative admissible shifts.
-/
namespace jacobi.EdgeResolvent
noncomputable section
open Real Set Filter
open scoped Topology

/-- The genuine normalized Bessel spectral function is real analytic on the entire real spectral axis.
Use: shiftedMass_analytic applies the actual adjacent-order quotient formula on its full real shifted domain, including zero and negative admissible shifts.
Article: jacobi, Appendix E.1.
Source: restriction of an entire complex function to the real axis, mathlib AnalyticAt.re_ofReal.
Proof: restrict the already proved actual entire normalized Bessel function and take its real part, which is exactly the existing real spectral normalization. -/
theorem realNormalized_analytic (a x:ℝ) : AnalyticAt ℝ (jacobi.Bessel.realNormalized a) x :=
  (jacobi.Bessel.normalized_analytic (a:ℂ) (x:ℂ)).re_ofReal

/-- The actual convergent shifted spectral mass is real analytic throughout its complete original admissible real-shift interval.
Use: shiftedSecond_analytic supplies actual analytic shifted moments to the off-edge calibration problem, without postulating regularity of their infinite sums.
Article: jacobi, Appendix E.1.
Proof: both genuine adjacent-order Bessel factors are real analytic after the original affine spectral substitution. The actual denominator is strictly positive by its proved positive canonical product. Their analytic quotient agrees locally with the actual convergent mass series by the already proved exact mass identity. -/
theorem shiftedMass_analytic (a:ℝ) (ha:-1<a) {w:ℝ}
    (hw: - jacobi.Bessel.sigma a ha 0<w) : AnalyticAt ℝ (shiftedMass a ha) w := by
  -- The positive original determinant excludes every possible quotient pole in this same full source interval.
  have hF : 0< jacobi.Bessel.realNormalized a (-w) := (shiftedLogDet_value a ha hw) ▸ exp_pos _
  have hn := (realNormalized_analytic (a+1) (-w)).comp (f:=fun x:ℝ => -x) analyticAt_id.neg
  have hd := (realNormalized_analytic a (-w)).comp (f:=fun x:ℝ => -x) analyticAt_id.neg
  have hden : AnalyticAt ℝ (fun x:ℝ => 2*(a+1)* jacobi.Bessel.realNormalized a (-x)) w := analyticAt_const.mul hd
  have ht := hn.div hden (mul_pos (by linarith : 0<2*(a+1)) hF).ne'
  apply ht.congr
  filter_upwards [Ioi_mem_nhds hw] with x hx
  exact (shiftedMass_quotient a ha hx).symm

/-- The actual convergent second shifted spectral moment is real analytic on the full original admissible real-shift interval.
Use: the original second-moment off-edge calibrations can vary the shift analytically while retaining the same actual spectral constraints.
Article: jacobi, Appendix E.1.
Proof: the actual mass is analytic, hence so is its genuine ordinary derivative. Multiply by -2 and use the independently proved exact local derivative identity for the original second-moment series. -/
theorem shiftedSecond_analytic (a:ℝ) (ha:-1<a) {w:ℝ}
    (hw: - jacobi.Bessel.sigma a ha 0<w) : AnalyticAt ℝ (shiftedSecond a ha) w := by
  have ht : AnalyticAt ℝ (fun x:ℝ => -2*deriv (shiftedMass a ha) x) w :=
    analyticAt_const.mul (shiftedMass_analytic a ha hw).deriv
  apply ht.congr
  filter_upwards [Ioi_mem_nhds hw] with x hx
  exact (shiftedSecond_eq_deriv a ha hx).symm

end
end jacobi.EdgeResolvent
