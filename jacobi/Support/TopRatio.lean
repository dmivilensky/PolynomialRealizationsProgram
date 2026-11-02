import jacobi.Support.TopSineProducts

/-!
Article: jacobi, Appendix C.3 (top-node polynomials).
The genuine adjacent top-node squared ratio is exactly a product of
three original shifted sine quotients at the same positive index.
This permits a direct first-difference estimate for the actual wave.
Use: topRatio_error applies the proved O(1/(m+1)) sine-quotient errors directly to the actual original top-node squared ratio.
-/
namespace jacobi.Support
noncomputable section
open Real jacobi.Reference

/-- The actual original top-node birth/death ratio is a product of three genuine shifted sine ratios at original positive index m+1.
Use: topRatio_error applies the proved O(1/(m+1)) sine-quotient errors directly to the actual original top-node squared ratio.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: the exact original coefficient ratio cancels its two common unit-step sine divisors, which are genuinely positive in the original nonterminal row range. -/
theorem topRatio_product {a b : ℝ} (ha:-1<a) (hb:-1<b) {n m : ℕ} (hm:m<n) :
    coefficientA a b (n+1) m/coefficientC a b (n+1) (m+1)=
      (sin (((m:ℝ)+1+(gamma a-1/2))*step a b (n+1))/sin (((m:ℝ)+1+(gamma b-1/2))*step a b (n+1)))*
      (sin (((m:ℝ)+1+(2*averageGamma a b-1))*step a b (n+1))/sin (((m:ℝ)+1)*step a b (n+1)))*
      (sin (((m:ℝ)+1+averageGamma a b)*step a b (n+1))/sin (((m:ℝ)+1+(averageGamma a b-1))*step a b (n+1))) := by
  -- The genuine unit-step sine is positive, so its two original quotient occurrences cancel without an exceptional parameter restriction.
  have hg := parameter_pos ha hb
  have hm0 := Nat.cast_nonneg m (α:=ℝ)
  have hmn : (m:ℝ)+1≤n := by exact_mod_cast (show m+1≤n by omega)
  have hf := frequency_gamma a b (n+1)
  push_cast at hf
  have hsin : sin (((m:ℝ)+1)*step a b (n+1))≠0 :=
    ne_of_gt (sin_position_pos ha hb (by omega) (by positivity) (by linarith [hg.1,hg.2.1]))
  rw [coefficient_ratio_sine ha hb hm,div_div_div_cancel_right₀ hsin]
  ring_nf

/-- The genuine adjacent top-node squared values have exactly the original birth/death ratio, with their actual positive normalization retained.
Use: the first-difference estimate for the genuine top-node polynomial follows from topRatio_error and its proved positive values.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: use the proved exact original product formula at its two genuine adjacent degrees, split its last original factor, and cancel the same genuinely positive original top-node square. -/
theorem naturalPolynomial_top_square_succ {a b : ℝ} (ha:-1<a) (hb:-1<b) {n m : ℕ} (hm:m<n) :
    ((naturalPolynomial a b ha hb n (m+1)).eval (cos (gamma a*step a b (n+1))))^2=
      ((naturalPolynomial a b ha hb n m).eval (cos (gamma a*step a b (n+1))))^2*
        (coefficientA a b (n+1) m/coefficientC a b (n+1) (m+1)) := by
  rw [naturalPolynomial_top_sq_ratio ha hb (by omega),Finset.prod_range_succ,
    naturalPolynomial_top_sq_ratio ha hb (by omega)]

end
end jacobi.Support
