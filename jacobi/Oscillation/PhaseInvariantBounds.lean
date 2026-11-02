import jacobi.Oscillation.PhaseInvariant

/-!
Article: jacobi, Proposition B.1.
The exact modified-phase derivative has a uniform integrable fourth-order
bound. At an actual original zero its sine corrections have their exact
values. These are the two quantitative inputs to McMahon's cubic estimate.
Use: its actual finite-interval integral has a uniform cubic tail bound, independently of the original zero index.
-/
namespace jacobi.Oscillation
noncomputable section
open Real Set
set_option backward.isDefEq.respectTransparency false

/-- The exact corrected-phase derivative is bounded by a fixed multiple of x^(-4) on the full large-argument range.
Use: its actual finite-interval integral has a uniform cubic tail bound, independently of the original zero index.
Article: jacobi, Proposition B.1.
Proof: sine and cosine have absolute value at most one. Bound the three
literal remainder terms separately, compare x^(-5) with x^(-4) for x>=1,
and combine the original scalar coefficients. -/
theorem phaseInvariantSlope_bound (c : ℝ) (theta : ℝ → ℝ) {x : ℝ} (hx : 1≤x) :
    |phaseInvariantSlope c theta x|≤(c^2+|c|)/x^4 := by
  -- The bound applies to the exact derivative already proved for the actual phase, without any oscillatory averaging premise.
  have hxp : 0<x := by linarith
  have hs : sin (theta x)^2≤1 := by nlinarith [Real.sin_sq_add_cos_sq (theta x),sq_nonneg (cos (theta x))]
  have hu : |cos (2*theta x)*sin (theta x)^2|≤1 := by
    rw [abs_mul,abs_of_nonneg (sq_nonneg (sin (theta x)))]
    calc
      _ ≤ 1*sin (theta x)^2 := mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (sq_nonneg _)
      _ ≤ 1 := by simpa only [one_mul] using hs
  have hv : |sin (2*theta x)*sin (theta x)^2|≤1 := by
    rw [abs_mul,abs_of_nonneg (sq_nonneg (sin (theta x)))]
    calc
      _ ≤ 1*sin (theta x)^2 := mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (sq_nonneg _)
      _ ≤ 1 := by simpa only [one_mul] using hs
  have hw : |cos (2*theta x)|≤1 := Real.abs_cos_le_one _
  have he : phaseInvariantSlope c theta x=
      c^2/(2*x^4)*(cos (2*theta x)*sin (theta x)^2)+
        c^2/(2*x^5)*(sin (2*theta x)*sin (theta x)^2)+
          (3*c/(4*x^4))*cos (2*theta x) := by
    unfold phaseInvariantSlope
    ring
  have h1 : |c^2/(2*x^4)*(cos (2*theta x)*sin (theta x)^2)|≤c^2/(2*x^4) := by
    rw [abs_mul,abs_of_nonneg (by positivity : 0≤c^2/(2*x^4))]
    exact (mul_le_mul_of_nonneg_left hu (by positivity)).trans_eq (mul_one _)
  have h2 : |c^2/(2*x^5)*(sin (2*theta x)*sin (theta x)^2)|≤c^2/(2*x^5) := by
    rw [abs_mul,abs_of_nonneg (by positivity : 0≤c^2/(2*x^5))]
    exact (mul_le_mul_of_nonneg_left hv (by positivity)).trans_eq (mul_one _)
  have h3 : |(3*c/(4*x^4))*cos (2*theta x)|≤3*|c|/(4*x^4) := by
    rw [abs_mul,abs_div,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3),
      abs_of_pos (show (0:ℝ)<4*x^4 by positivity)]
    exact (mul_le_mul_of_nonneg_left hw (by positivity)).trans_eq (mul_one _)
  have hp : x^4≤x^5 := by
    calc
      _ = x^4*1 := (mul_one _).symm
      _ ≤ x^4*x := mul_le_mul_of_nonneg_left hx (pow_nonneg hxp.le 4)
      _ = _ := by ring
  have hd : c^2/(2*x^5)≤c^2/(2*x^4) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤2))
  have he3 : 3*|c|/(4*x^4)≤ |c|/x^4 := by
    have hh := mul_le_mul_of_nonneg_right (show (3/4:ℝ)≤1 by norm_num) (show 0≤ |c|/x^4 by positivity)
    convert hh using 1 <;> ring
  rw [he]
  calc
    _ ≤ |c^2/(2*x^4)*(cos (2*theta x)*sin (theta x)^2)|+
        |c^2/(2*x^5)*(sin (2*theta x)*sin (theta x)^2)|+|(3*c/(4*x^4))*cos (2*theta x)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ c^2/(2*x^4)+c^2/(2*x^5)+3*|c|/(4*x^4) := add_le_add (add_le_add h1 h2) h3
    _ ≤ c^2/(2*x^4)+c^2/(2*x^4)+|c|/x^4 := add_le_add (add_le_add_right hd _) he3
    _ = _ := by field_simp [hxp.ne']; ring

/-- At an actual sine-zero phase level, the corrected phase has its precise nonoscillatory value.
Use: evaluates the original modified phase at each genuine Bessel zero before taking its exact indexed large-zero limit.
Article: jacobi, Proposition B.1.
Proof: the genuine sine vanishes, so its double-angle sine vanishes and
its double-angle cosine equals one. Substitute those exact identities. -/
theorem phaseInvariant_at_zero {c x : ℝ} {theta : ℝ → ℝ} (hs : sin (theta x)=0) :
    phaseInvariant c theta x=theta x-x+c/(2*x)-c/(4*x^3) := by
  unfold phaseInvariant
  simp only [Real.sin_two_mul,Real.cos_two_mul_eq_one_sub,hs,mul_zero,zero_mul,zero_div,
    add_zero,zero_pow (by norm_num : 2≠0),sub_zero,mul_one]

end
end jacobi.Oscillation
