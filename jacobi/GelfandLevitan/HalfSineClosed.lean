import jacobi.GelfandLevitan.HalfSineCase
import Mathlib.NumberTheory.ZetaValues

/-!
Article: jacobi, Section 3.2 (sharp comparison at U).
The actual constructed persymmetric profile is exactly 2*t*(1-t),
and its original squared integral is exactly 2/15.
The existing community Fourier expansion of the second Bernoulli
polynomial evaluates the genuine original sine series; no new Fourier
completeness proof or numerical certification is introduced.
Use: half_sine_persymmetricProfile evaluates the constructed original source profile, rather than specifying a replacement parabola.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory jacobi.Reference
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false

/-- The actual original sine-square series has the exact parabola sum on the whole closed physical interval.
Use: half_sine_persymmetricProfile evaluates the constructed original source profile, rather than specifying a replacement parabola.
Article: jacobi, Section 3.2 (sharp comparison at U).
Source: the Fourier series of the second Bernoulli polynomial and Euler's zeta(2) identity, proved in mathlib as hasSum_one_div_nat_pow_mul_cos and hasSum_zeta_two.
Proof: subtract the genuine cosine Fourier series from the genuine
zeta(2) series and multiply by 2/pi^2. The exact double-angle identity
turns every original summand into the source sine square; the zero initial term is removed exactly. -/
theorem sine_square_series {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    HasSum (fun k:ℕ => 4*(Real.sin (Real.pi*(k+1:ℝ)*t))^2/(Real.pi^2*(k+1:ℝ)^2))
      (2*t*(1-t)) := by
  -- Both Fourier sums already converge genuinely, including at the two physical endpoints.
  have hcos : HasSum (fun n:ℕ => (1/(n:ℝ)^2)*Real.cos (2*Real.pi*n*t))
      (Real.pi^2*(t^2-t+1/6)) := by
    have h := hasSum_one_div_nat_pow_mul_cos (k := 1) (by decide) ht
    change HasSum _ (((-1:ℝ)^(1+1)*(2*Real.pi)^(2*1)/2/(2*1).factorial)*bernoulliFun (2*1) t) at h
    rw [show (2:ℕ)*1=2 by decide,bernoulliFun_two] at h
    norm_num only [Nat.reduceAdd,Nat.factorial_two,Nat.cast_ofNat,neg_one_sq] at h
    convert! h using 1
    ring
  have h : HasSum (fun n:ℕ => 4*(Real.sin (Real.pi*n*t))^2/(Real.pi^2*(n:ℝ)^2))
      (2*t*(1-t)) := by
    convert! (hasSum_zeta_two.sub hcos).mul_left (2/Real.pi^2) using 1
    · funext n
      rw [show 2*Real.pi*(n:ℝ)*t=2*(Real.pi*n*t) by ring,Real.cos_two_mul_eq_one_sub]
      simp only [div_eq_mul_inv,mul_inv]
      ring
    · field_simp [Real.pi_ne_zero]
      ring
  simpa only [Finset.sum_range_one,Nat.cast_zero,mul_zero,zero_mul,Real.sin_zero,zero_pow (by decide : (2:ℕ)≠0),
    zero_div,sub_zero,Nat.cast_add,Nat.cast_one] using (hasSum_nat_add_iff' 1).mpr h

/-- The actual constructed persymmetric profile at order 1/2 is exactly the article's original parabola at every physical point.
Use: half_sine_persymmetricConstant evaluates the same original squared-profile integral as 2/15.
Article: jacobi, Section 3.2 (sharp comparison at U).
Proof: the actual GL construction has its proved original sine series;
the genuine Bernoulli Fourier identity evaluates that same series on the entire closed interval. -/
theorem half_sine_persymmetricProfile (ha : -1<(1/2:ℝ)) (t : Interval) :
    persymmetricProfile (1/2) ha t=2*(t:ℝ)*(1-(t:ℝ)) := by
  rw [half_sine_persymmetricSeries]
  exact (sine_square_series t.property).tsum_eq

/-- The actual original persymmetric constant at order 1/2 is exactly 2/15.
Use: closes the exact constant in the alpha=1/2 special case of Proposition C.2, with no numerical premise or replacement profile definition.
Article: jacobi, Section 3.2 (sharp comparison at U).
Proof: substitute the proved actual parabola profile in its original
Lebesgue squared integral. The genuine polynomial primitive
4*t^3/3-2*t^4+4*t^5/5 evaluates its exact integral as 2/15. -/
theorem half_sine_persymmetricConstant (ha : -1<(1/2:ℝ)) :
    persymmetricConstant (1/2) ha=2/15 := by
  -- The actual subtype interval integral is the original interval integral because both endpoints are null.
  unfold persymmetricConstant
  simp_rw [half_sine_persymmetricProfile]
  rw [integral_subtype (s := Icc (0:ℝ) 1) measurableSet_Icc (fun t:ℝ => (2*t*(1-t))^2),
    integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  have hd (x : ℝ) : HasDerivAt (fun t:ℝ => (4/3)*t^3-2*t^4+(4/5)*t^5) ((2*x*(1-x))^2) x := by
    convert! ((((hasDerivAt_id x).pow 3).const_mul (4/3)).sub
      (((hasDerivAt_id x).pow 4).const_mul 2)).add
        (((hasDerivAt_id x).pow 5).const_mul (4/5)) using 1
    norm_num
    ring
  have hc : Continuous (fun t:ℝ => (2*t*(1-t))^2) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hc.intervalIntegrable (μ := volume) 0 1)]
  norm_num

end
end jacobi.GelfandLevitan
