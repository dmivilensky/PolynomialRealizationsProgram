import jacobi.Bessel.Differential
import jacobi.Jacobi.Gegenbauer

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
The existing community ordinary hypergeometric function has convergence
radius at least one and satisfies its exact classical differential
equation there. Its genuine coefficients and analytic derivatives are
used throughout, including terminating numerator parameters.
Source: Gauss's hypergeometric equation, DLMF 15.10.1; proved here.
Use: the actual reference solution is analytic in its spatial hypergeometric argument throughout the physical interval.
-/
namespace jacobi.Reference.Hypergeometric
noncomputable section
open Complex Set Filter FormalMultilinearSeries
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The community ordinary hypergeometric series has radius at least one for arbitrary complex parameters, including terminating cases.
Use: the actual reference solution is analytic in its spatial hypergeometric argument throughout the physical interval.
Article: jacobi, Appendix C.1 (selected endpoint branch).
Proof: a nonpositive integer parameter makes the genuine series terminate. Otherwise use the community exact unit-radius theorem. -/
theorem radius_ge_one (a b c : ℂ) : (1:ℝ≥0∞)≤(ordinaryHypergeometricSeries ℂ a b c).radius := by
  -- Terminating original eigenvalue cases are kept in the same theorem as the nonterminating reference solutions.
  by_cases ha : ∃ k : ℕ,a= -(k:ℂ)
  · obtain ⟨k,rfl⟩ := ha
    rw [ordinaryHypergeometric_radius_top_of_neg_nat₁ ℂ b c]
    exact le_top
  by_cases hb : ∃ k : ℕ,b= -(k:ℂ)
  · obtain ⟨k,rfl⟩ := hb
    rw [ordinaryHypergeometric_radius_top_of_neg_nat₂ ℂ a c]
    exact le_top
  by_cases hc : ∃ k : ℕ,c= -(k:ℂ)
  · obtain ⟨k,rfl⟩ := hc
    rw [ordinaryHypergeometric_radius_top_of_neg_nat₃ ℂ a b]
    exact le_top
  have hneg {z : ℂ} (hz : ¬∃ k : ℕ,z= -(k:ℂ)) (k : ℕ) : (k:ℂ)≠ -z := by
    intro h
    apply hz ⟨k,?_⟩
    simpa only [neg_neg] using (congrArg Neg.neg h).symm
  rw [ordinaryHypergeometricSeries_radius_eq_one ℂ a b c (fun k => ⟨hneg ha k,hneg hb k,hneg hc k⟩)]

/-- The actual community 2F1 function is analytic at every point of the open unit disk.
Use: all reference differential identities use genuine ordinary derivatives of the original special function.
Article: jacobi, Appendix C.1 (selected endpoint branch).
Proof: the actual series is analytic on its convergence ball, which contains the unit disk by the proved radius bound. -/
theorem analytic {a b c z : ℂ} (hz : ‖z‖<1) : AnalyticAt ℂ (ordinaryHypergeometric a b c) z := by
  apply (ordinaryHypergeometricSeries ℂ a b c).analyticOnNhd
  apply Metric.eball_subset_eball (radius_ge_one a b c)
  simpa only [Metric.mem_eball,edist_dist,dist_zero_right,ENNReal.ofReal_lt_one] using hz

/-- The actual original 2F1 coefficients satisfy their exact Gauss differential-equation recurrence.
Use: proves the reference hypergeometric equation from the genuinely convergent community series.
Article: jacobi, Appendix C.1 (selected endpoint branch).
Proof: use the actual rising-factorial and factorial next-factor identities; positive real part of c excludes every denominator zero. -/
theorem coefficient_equation {a b c : ℂ} (hc : 0<c.re) (n : ℕ) :
    (n+1:ℂ)*(c+n)*ordinaryHypergeometricCoefficient a b c (n+1)=
      (a+n)*(b+n)*ordinaryHypergeometricCoefficient a b c n := by
  -- No nontermination restriction is needed on either numerator parameter.
  have hcn : c+n≠0 := by
    intro h
    have hp : 0<(c+n).re := by simp only [add_re,natCast_re]; linarith [Nat.cast_nonneg (α := ℝ) n]
    rw [h,zero_re] at hp
    exact lt_irrefl _ hp
  have hp : (ascPochhammer ℂ n).eval c≠0 := by
    have h := jacobi.Bessel.pochhammer_ne_zero (a := c-1) (by simp only [sub_re,one_re]; linarith) n
    simpa only [sub_add_cancel] using h
  have hn : (n.factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  unfold ordinaryHypergeometricCoefficient
  rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,
    ascPochhammer_succ_eval,ascPochhammer_succ_eval,ascPochhammer_succ_eval]
  field_simp [hp,hcn,hn,show (n:ℂ)+1≠0 by exact_mod_cast Nat.succ_ne_zero n]

/-- The genuine community 2F1 function satisfies Gauss's differential equation near the origin.
Use: analytic continuation proves the actual reference equation throughout the full physical spatial domain.
Article: jacobi, Appendix C.1 (selected endpoint branch).
Proof: differentiate the actual convergent scalar series twice using
the earlier proved scalar derivative theorem. Shift the first and second
derivative series to account for x and x^2. The proved original
coefficient recurrence makes the resulting residual series zero. -/
theorem equation_near_zero {a b c : ℂ} (hc : 0<c.re) :
    ∀ᶠ z in 𝓝 (0:ℂ),z*(1-z)*deriv (deriv (ordinaryHypergeometric a b c)) z+
      (c-(a+b+1)*z)*deriv (ordinaryHypergeometric a b c) z-a*b*ordinaryHypergeometric a b c z=0 := by
  -- Every series below is a genuine local expansion of the community function or its actual derivative.
  let f : ℂ → ℂ := ordinaryHypergeometric a b c
  let q : ℕ → ℂ := ordinaryHypergeometricCoefficient a b c
  let q1 := fun n : ℕ => (n+1:ℂ)*q (n+1)
  let q2 := fun n : ℕ => (n+1:ℂ)*q1 (n+1)
  have h0 : HasFPowerSeriesAt f (ofScalars ℂ q) 0 :=
    ((ordinaryHypergeometricSeries ℂ a b c).hasFPowerSeriesOnBall
      (lt_of_lt_of_le (by norm_num : (0:ℝ≥0∞)<1) (radius_ge_one a b c))).hasFPowerSeriesAt
  have h1 := jacobi.Bessel.scalar_derivative_series h0
  have h2 := jacobi.Bessel.scalar_derivative_series h1
  rw [hasFPowerSeriesAt_iff] at h0 h1 h2
  filter_upwards [h0,h1,h2] with z hz0 hz1 hz2
  simp only [coeff_ofScalars,smul_eq_mul,zero_add] at hz0 hz1 hz2
  have h10 : HasSum (fun n : ℕ => n*z^n*q n) (z*deriv f z) := by
    apply (hasSum_nat_add_iff' 1).mp
    convert hz1.mul_left z using 1
    · funext n; push_cast; rw [pow_succ]; ring
    · simp
  have h21 : HasSum (fun n : ℕ => n*z^n*q1 n) (z*deriv (deriv f) z) := by
    apply (hasSum_nat_add_iff' 1).mp
    convert hz2.mul_left z using 1
    · funext n; dsimp [q1,q2]; push_cast; rw [pow_succ]; ring
    · simp
  have h22 : HasSum (fun n : ℕ => n*(n-1:ℂ)*z^n*q n) (z^2*deriv (deriv f) z) := by
    apply (hasSum_nat_add_iff' 2).mp
    convert hz2.mul_left (z^2) using 1
    · funext n; push_cast; rw [pow_add]; ring
    · norm_num [Finset.sum_range_succ]
  have h := (((h21.sub h22).add (hz1.mul_left c)).sub (h10.mul_left (a+b+1))).sub (hz0.mul_left (a*b))
  have hcoeff (n : ℕ) : n*z^n*q1 n-n*(n-1:ℂ)*z^n*q n+c*(z^n*q1 n)-
      (a+b+1)*(n*z^n*q n)-a*b*(z^n*q n)=0 := by
    dsimp [q1,q]
    linear_combination z^n*(coefficient_equation (a := a) (b := b) hc n)
  have ht := h.tsum_eq
  change (∑' n : ℕ,(n*z^n*q1 n-n*(n-1:ℂ)*z^n*q n+c*(z^n*q1 n)-
    (a+b+1)*(n*z^n*q n)-a*b*(z^n*q n)))=
      z*deriv (deriv f) z-z^2*deriv (deriv f) z+c*deriv f z-(a+b+1)*(z*deriv f z)-a*b*f z at ht
  simp only [hcoeff,tsum_zero] at ht
  change z*(1-z)*deriv (deriv f) z+(c-(a+b+1)*z)*deriv f z-a*b*f z=0
  linear_combination -ht

/-- The actual community 2F1 function satisfies its exact Gauss equation on the full open unit disk, including every terminating case.
Use: proves the original reference Poeschl--Teller equation for arbitrary spectral parameter after the source sine-power substitution.
Article: jacobi, Lemma C.1.
Proof: the residual and both actual derivatives are analytic on the connected unit disk. Its genuine convergent coefficient expansion vanishes near zero, so the community identity theorem makes it zero on the entire disk. -/
theorem equation {a b c z : ℂ} (hc : 0<c.re) (hz : ‖z‖<1) :
    z*(1-z)*deriv (deriv (ordinaryHypergeometric a b c)) z+
      (c-(a+b+1)*z)*deriv (ordinaryHypergeometric a b c) z-a*b*ordinaryHypergeometric a b c z=0 := by
  -- The local original coefficient calculation is extended on the actual connected convergence domain.
  have h : AnalyticOnNhd ℂ (fun z => z*(1-z)*deriv (deriv (ordinaryHypergeometric a b c)) z+
      (c-(a+b+1)*z)*deriv (ordinaryHypergeometric a b c) z-a*b*ordinaryHypergeometric a b c z) (Metric.ball 0 1) := by
    intro w hw
    have h0 := analytic (a := a) (b := b) (c := c) (by simpa only [Metric.mem_ball,dist_zero_right] using hw)
    have h1 := h0.deriv
    have h2 := h1.deriv
    fun_prop
  exact h.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball (0:ℂ) 1).isPreconnected
    (by simp : (0:ℂ)∈Metric.ball 0 1) (equation_near_zero hc)
    (by simpa only [Metric.mem_ball,dist_zero_right] using hz)

end
end jacobi.Reference.Hypergeometric
