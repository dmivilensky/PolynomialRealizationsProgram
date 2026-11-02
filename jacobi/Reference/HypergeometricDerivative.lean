import jacobi.Reference.Hypergeometric
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
The genuine derivative of the community Gauss function is its shifted
Gauss function, with the exact factor a*b/c. The statement includes
terminating numerator parameters. It is needed for the actual spatial
midpoint slope, rather than a separately defined formal slope.
Source: the hypergeometric derivative formula, DLMF 15.5.1.
Use: identifies the actual derivative series in derivative_shift.
-/
namespace jacobi.Reference.Hypergeometric
noncomputable section
open Set Filter _root_.Complex Polynomial FormalMultilinearSeries
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false

/-- Differentiating each genuine Gauss coefficient gives exactly its shifted-parameter coefficient.
Use: identifies the actual derivative series in derivative_shift.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Source: DLMF 15.5.1, the Pochhammer proof of the hypergeometric derivative identity.
Proof: the left rising-factorial recurrence extracts a, b and c;
the factorial recurrence cancels the derivative's n+1. Positive real
part of c excludes every denominator zero; no numerator is cancelled. -/
theorem derivative_coefficient {a b c : ℂ} (hc : 0<c.re) (n : ℕ) :
    (n+1:ℂ)*ordinaryHypergeometricCoefficient a b c (n+1)=
      (a*b/c)*ordinaryHypergeometricCoefficient (a+1) (b+1) (c+1) n := by
  have hc0 : c≠0 := by intro h; simp only [h,zero_re,lt_self_iff_false] at hc
  have hp : (ascPochhammer ℂ n).eval (c+1)≠0 :=
    jacobi.Bessel.pochhammer_ne_zero (a := c) (by linarith) n
  have hn : (n.factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  unfold ordinaryHypergeometricCoefficient
  simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,
    ascPochhammer_succ_left,eval_mul,eval_X,eval_comp,eval_add,eval_one]
  field_simp

/-- The actual Gauss derivative is the exact shifted-parameter Gauss function throughout the open convergence disk.
Use: differentiates the actual midpoint reference wave before applying second_summation at the shifted reference exponent.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Source: the hypergeometric derivative identity, DLMF 15.5.1, proved here for actual analytic functions.
Proof: differentiate the genuine convergent scalar series near zero
and identify each coefficient with derivative_coefficient. Both actual
functions are analytic on the whole unit disk; the identity theorem
extends the local series equality throughout that connected disk. -/
theorem derivative_shift {a b c z : ℂ} (hc : 0<c.re) (hz : ‖z‖<1) :
    deriv (ordinaryHypergeometric a b c) z=
      (a*b/c)*ordinaryHypergeometric (a+1) (b+1) (c+1) z := by
  -- The two local series genuinely expand the original functions and their ordinary derivative.
  have hs {u v w : ℂ} : HasFPowerSeriesAt (ordinaryHypergeometric u v w)
      (ofScalars ℂ (ordinaryHypergeometricCoefficient u v w)) 0 :=
    ((ordinaryHypergeometricSeries ℂ u v w).hasFPowerSeriesOnBall
      (lt_of_lt_of_le (by norm_num : (0:ℝ≥0∞)<1) (radius_ge_one u v w))).hasFPowerSeriesAt
  have hd := jacobi.Bessel.scalar_derivative_series (hs (u := a) (v := b) (w := c))
  have hg := hs (u := a+1) (v := b+1) (w := c+1)
  rw [hasFPowerSeriesAt_iff] at hd hg
  have hnear : deriv (ordinaryHypergeometric a b c)=ᶠ[𝓝 (0:ℂ)]
      (fun w => (a*b/c)*ordinaryHypergeometric (a+1) (b+1) (c+1) w) := by
    filter_upwards [hd,hg] with w hwd hwg
    simp only [coeff_ofScalars,smul_eq_mul,zero_add] at hwd hwg
    have h := hwg.mul_left (a*b/c)
    apply hwd.unique
    convert! h using 1
    funext n
    linear_combination w^n*derivative_coefficient (a := a) (b := b) hc n
  have hF : AnalyticOnNhd ℂ (deriv (ordinaryHypergeometric a b c:ℂ → ℂ)) (Metric.ball (0:ℂ) 1) :=
    fun w hw => (analytic (a := a) (b := b) (c := c)
      (by simpa only [Metric.mem_ball,dist_zero_right] using hw)).deriv
  have hG : AnalyticOnNhd ℂ
      (fun w : ℂ => (a*b/c)*ordinaryHypergeometric (a+1) (b+1) (c+1) w) (Metric.ball (0:ℂ) 1) :=
    fun w hw => analyticAt_const.mul (analytic
      (by simpa only [Metric.mem_ball,dist_zero_right] using hw))
  exact hF.eqOn_of_preconnected_of_eventuallyEq hG (convex_ball (0:ℂ) 1).isPreconnected
    (by simp : (0:ℂ)∈Metric.ball 0 1) hnear
      (by simpa only [Metric.mem_ball,dist_zero_right] using hz)

end
end jacobi.Reference.Hypergeometric
