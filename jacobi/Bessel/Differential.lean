import jacobi.Bessel.Convergence
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
The actual normalized entire Bessel function satisfies its differential
equation. Termwise differentiation uses genuine analytic power series;
the identity theorem extends the local coefficient calculation globally.
Source: the Bessel equation in the squared spectral variable and the
identity theorem for holomorphic functions.
Use: converts the verified Bessel coefficient recurrence into an equation for the actual function.
-/
namespace jacobi.Bessel
noncomputable section
open Complex Set Filter FormalMultilinearSeries
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- A genuine scalar power series differentiates to the genuine series with coefficients (n+1)*b(n+1).
Use: converts the verified Bessel coefficient recurrence into an equation for the actual function.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: differentiate the actual multilinear analytic series, apply the
continuous linear evaluation map at one and compute its true scalar
coefficients. This is analytic differentiation, not manipulation of a formal sum. -/
theorem scalar_derivative_series {f : ℂ → ℂ} {b : ℕ → ℂ}
    (h : HasFPowerSeriesAt f (ofScalars ℂ b) 0) :
    HasFPowerSeriesAt (deriv f) (ofScalars ℂ (fun n => (n+1:ℂ)*b (n+1))) 0 := by
  -- The analytic derivative theorem supplies a convergent series on the same actual ball.
  obtain ⟨r,hr⟩ := h
  let T := ContinuousLinearMap.apply ℂ ℂ (1:ℂ)
  have hd := (T.comp_hasFPowerSeriesOnBall hr.fderiv).hasFPowerSeriesAt
  have he (n : ℕ) :
      (T.compFormalMultilinearSeries (ofScalars ℂ b).derivSeries).coeff n=(n+1:ℂ)*b (n+1) := by
    change (ofScalars ℂ b).derivSeries.coeff n 1=(n+1:ℂ)*b (n+1)
    rw [derivSeries_coeff_one,coeff_ofScalars]
    simp only [nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  rw [hasFPowerSeriesAt_iff] at hd ⊢
  filter_upwards [hd] with z hz
  simpa only [coeff_ofScalars,he,T,Function.comp_apply,ContinuousLinearMap.apply_apply,
    fderiv_apply_one_eq_deriv] using hz

/-- The defined normalized Bessel function has the literal coefficient series in the analytic sense at zero.
Use: actual analytic differentiation may now use the previously verified coefficient recurrence.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: its already proved HasSum at every complex point implies the
neighborhood power-series criterion with the same scalar coefficients. -/
theorem normalized_powerSeries (a : ℂ) :
    HasFPowerSeriesAt (normalized a) (ofScalars ℂ (coefficient a)) 0 := by
  rw [hasFPowerSeriesAt_iff]
  exact Eventually.of_forall fun z => by
    simpa only [coeff_ofScalars,smul_eq_mul,mul_comm,zero_add] using normalized_hasSum a z

/-- The genuine normalized Bessel function satisfies its differential equation near the origin.
Use: analytic continuation establishes the actual equation at every spectral point.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: differentiate the genuine convergent coefficient series twice.
Shift the second derivative series once to account for multiplication by z.
The already verified recurrence makes every coefficient of the resulting
convergent residual series zero, so its actual sum vanishes. -/
theorem normalized_equation_near_zero {a : ℂ} (ha : -1<a.re) :
    ∀ᶠ z in 𝓝 (0:ℂ),
      4*z*deriv (deriv (normalized a)) z+4*(a+1)*deriv (normalized a) z+normalized a z=0 := by
  -- Both differentiated series are convergent analytic expansions of the actual derivatives.
  let b1 := fun n : ℕ => (n+1:ℂ)*coefficient a (n+1)
  let b2 := fun n : ℕ => (n+1:ℂ)*b1 (n+1)
  have h0 := normalized_powerSeries a
  have h1 : HasFPowerSeriesAt (deriv (normalized a)) (ofScalars ℂ b1) 0 := scalar_derivative_series h0
  have h2 : HasFPowerSeriesAt (deriv (deriv (normalized a))) (ofScalars ℂ b2) 0 :=
    scalar_derivative_series h1
  rw [hasFPowerSeriesAt_iff] at h0 h1 h2
  filter_upwards [h0,h1,h2] with z hz0 hz1 hz2
  simp only [coeff_ofScalars,smul_eq_mul,zero_add] at hz0 hz1 hz2
  have hshift : HasSum (fun n : ℕ => 4*n*z^n*b1 n)
      (4*z*deriv (deriv (normalized a)) z) := by
    -- The missing constant term is exactly zero, so the index shift has no boundary contribution.
    apply (hasSum_nat_add_iff' 1).mp
    have h := hz2.mul_left (4*z)
    convert h using 1
    · funext n
      simp only [b2,Nat.cast_add,Nat.cast_one,pow_succ]
      ring
    · simp only [Finset.sum_range_one,Nat.cast_zero,mul_zero,zero_mul,sub_zero]
  have h := (hshift.add (hz1.mul_left (4*(a+1)))).add hz0
  have he (n : ℕ) : 4*n*z^n*b1 n+4*(a+1)*(z^n*b1 n)+z^n*coefficient a n=0 := by
    dsimp only [b1]
    linear_combination z^n*(coefficient_equation ha n)
  have hs := h.tsum_eq
  simp only [he,tsum_zero] at hs
  exact hs.symm

/-- The actual normalized entire Bessel function satisfies its spectral differential equation everywhere.
Use: proves simplicity and spectral properties of its true zeros, rather than of an abstract recurrence.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: the residual is entire because the function and both genuine
derivatives are analytic. Its convergent series vanishes near zero.
The identity theorem on the connected complex plane makes it zero everywhere. -/
theorem normalized_equation {a : ℂ} (ha : -1<a.re) (z : ℂ) :
    4*z*deriv (deriv (normalized a)) z+4*(a+1)*deriv (normalized a) z+normalized a z=0 := by
  -- A local power-series calculation is extended to the actual whole-plane analytic function.
  have h : AnalyticOnNhd ℂ
      (fun w => 4*w*deriv (deriv (normalized a)) w+4*(a+1)*deriv (normalized a) w+normalized a w)
      univ := by
    intro w _
    have h0 := normalized_analytic a w
    have h1 := h0.deriv
    have h2 := h1.deriv
    fun_prop
  exact h.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ 0)
    (normalized_equation_near_zero ha) (mem_univ z)

end
end jacobi.Bessel
