import jacobi.Young.Hyperbolic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
Article: jacobi, Proposition C.4.
Every positive multiple of sech^4 has the exact two-ended logarithmic
tail exponent -4. The proof is an elementary exponential sandwich;
it is independent of the separate endpoint asymptotics of the genuine
persymmetric density, which are still needed in Proposition C.4.
Use: young_tail transfers the proved positive-end estimate to both spatial ends.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Filter jacobi.Young
open scoped Topology

/-- The real hyperbolic secant is unchanged when its argument is replaced by its absolute value.
Use: young_tail transfers the proved positive-end estimate to both spatial ends.
Article: jacobi, Proposition C.4.
Proof: split the sign and use the actual even hyperbolic secant. -/
theorem sech_abs (x:ℝ) : sech |x|=sech x := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h,sech_neg]

/-- On the positive half-line the actual logarithmic cosh differs from x by at most log two.
Use: young_log_bounds gives an exact bounded error for the original logarithmic density tail.
Article: jacobi, Proposition C.4.
Proof: exp(x)/2 <= cosh(x) <= exp(x); the logarithm is increasing on positive numbers. -/
theorem log_cosh_bounds {x:ℝ} (hx:0≤x) : x-log 2≤log (cosh x) ∧ log (cosh x)≤x := by
  have hl : exp x/2≤cosh x := by rw [cosh_eq]; linarith [exp_pos (-x)]
  have hu : cosh x≤exp x := by
    rw [cosh_eq]
    have h := exp_le_exp.mpr (show -x≤x by linarith)
    linarith
  have hlog := Real.log_le_log (by positivity : 0<exp x/2) hl
  rw [Real.log_div (exp_pos x).ne' (by norm_num),Real.log_exp] at hlog
  exact ⟨hlog,by simpa only [Real.log_exp] using Real.log_le_log (cosh_pos x) hu⟩

/-- The original positive Young density has a bounded logarithmic error from its exact exponential tail.
Use: young_tail_atTop squeezes the true logarithmic quotient between two constant-over-x errors.
Article: jacobi, Proposition C.4.
Proof: take the logarithm of the actual positive product and fourth power,
then substitute the proved two-sided logarithmic cosh estimate. -/
theorem young_log_bounds {b x:ℝ} (hb:0<b) (hx:0≤x) :
    log b-4*x≤log (b*sech x^4) ∧ log (b*sech x^4)≤log b-4*x+4*log 2 := by
  have he : log (b*sech x^4)=log b-4*log (cosh x) := by
    rw [Real.log_mul hb.ne' (pow_ne_zero 4 (sech_pos x).ne'),Real.log_pow,sech,Real.log_inv]
    ring
  rw [he]
  obtain ⟨hl,hu⟩ := log_cosh_bounds hx
  constructor <;> linarith

/-- Every actual positive Young equality profile has exactly the source's logarithmic tail exponent at the positive end.
Use: young_tail yields both spatial ends, and Proposition C.4 compares this forced exponent with the genuine persymmetric one.
Article: jacobi, Proposition C.4.
Proof: the exact logarithmic sandwich has lower and upper errors
log(b)/x and (log(b)+4log(2))/x, both tending to zero. -/
theorem young_tail_atTop {b:ℝ} (hb:0<b) :
    Tendsto (fun x:ℝ => log (b*sech x^4)/x) atTop (𝓝 (-4)) := by
  -- The positive denominator is retained explicitly before dividing either original inequality.
  have hi : Tendsto (fun x:ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hl : Tendsto (fun x:ℝ => log b/x-4) atTop (𝓝 (-4)) := by
    simpa only [mul_zero,zero_sub,div_eq_mul_inv] using (hi.const_mul (log b)).sub_const 4
  have hu : Tendsto (fun x:ℝ => (log b+4*log 2)/x-4) atTop (𝓝 (-4)) := by
    simpa only [mul_zero,zero_sub,div_eq_mul_inv] using (hi.const_mul (log b+4*log 2)).sub_const 4
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    have h := (div_le_div_of_nonneg_right (young_log_bounds hb hx.le).1 hx.le)
    convert h using 1; field_simp
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    have h := (div_le_div_of_nonneg_right (young_log_bounds hb hx.le).2 hx.le)
    convert h using 1; field_simp; ring

/-- The actual centered Young equality profile has logarithmic tail exponent minus four at both spatial ends.
Use: the completed Young-minimizer classification gives the source's comparison exponent in Proposition C.4.
Article: jacobi, Proposition C.4.
Proof: compose the proved positive-end limit with norm tending to infinity
outside compact real sets, and use the exact evenness of the original profile. -/
theorem young_tail {b:ℝ} (hb:0<b) :
    Tendsto (fun x:ℝ => log (b*sech x^4)/|x|) (cocompact ℝ) (𝓝 (-4)) := by
  simpa only [Function.comp_def,Real.norm_eq_abs,sech_abs] using
    (young_tail_atTop hb).comp (tendsto_norm_cocompact_atTop (E:=ℝ))

end
end jacobi.Trichotomy
