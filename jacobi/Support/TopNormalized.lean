import jacobi.Support.Polynomials
import jacobi.Support.TopMonic

/-!
Article: jacobi, Appendix C.3 (top-node polynomials).
The genuine normalized support polynomial is positive at the actual top
node and has precisely the original product of birth/death ratios.
This fixes the branch used by reduction of order and the discrete
Volterra kernel; no independent positive solution is introduced.
Use: naturalPolynomial_top_pos and naturalPolynomial_top_sq_ratio provide the genuine positive reference solution for the support Volterra equation.
-/
namespace jacobi.Support
noncomputable section
open Real Polynomial jacobi.Reference jacobi.Finite chebyshev1 chebyshev2

/-- The genuine original normalized support value at the top node is the original monic amplitude divided by its actual coupling product.
Use: naturalPolynomial_top_pos and naturalPolynomial_top_sq_ratio provide the genuine positive reference solution for the support Volterra equation.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: evaluate the actual normalized continuant and insert the proved exact original monic top-node value. -/
theorem naturalPolynomial_top (a b : ℝ) (ha : -1<a) (hb : -1<b) (n m : ℕ) (hm:m≤n+1) :
    (naturalPolynomial a b ha hb n m).eval (cos (gamma a*step a b (n+1)))=
      topMonicAmplitude a b n m/(naturalChain a b ha hb (n+1)).data.linkProduct m := by
  rw [naturalPolynomial,normalizedLeading,Polynomial.eval_mul,Polynomial.eval_C,
    leading_top_node a b ha hb n m hm]
  ring

/-- The actual original support polynomial is strictly positive at its genuine top node throughout the entire nonterminal polynomial range.
Use: reduction of order uses this same actual top-node solution and divides only by its genuine positive values.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: the exact monic product and genuine interior coupling product are both strictly positive. -/
theorem naturalPolynomial_top_pos {a b : ℝ} (ha : -1<a) (hb : -1<b) {n m : ℕ} (hm:m≤n) :
    0<(naturalPolynomial a b ha hb n m).eval (cos (gamma a*step a b (n+1))) := by
  rw [naturalPolynomial_top a b ha hb n m (by omega)]
  exact div_pos (topMonicAmplitude_pos ha hb hm)
    (linkProduct_pos (naturalChain_irreducible a b ha hb (n+1)) (by omega))

/-- The genuine top-node normalization has exactly the original product of A/C ratios, with no unproved normalizing factor.
Use: the sine-product formula and its uniform estimates apply to the actual spectral orthogonal polynomial used later in the support Gram comparison.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: induction on the actual positive coupling product cancels the original A_m*C_(m+1)/4 against the squared next monic factor. Every cancelled birth and death factor is genuinely positive in the stated range. -/
theorem naturalPolynomial_top_sq_ratio {a b : ℝ} (ha : -1<a) (hb : -1<b) {n m : ℕ} (hm:m≤n) :
    ((naturalPolynomial a b ha hb n m).eval (cos (gamma a*step a b (n+1))))^2=
      ∏ j∈Finset.range m,coefficientA a b (n+1) j/coefficientC a b (n+1) (j+1) := by
  -- The induction keeps the original monic numerator and actual recurrence coupling denominator together.
  rw [naturalPolynomial_top a b ha hb n m (by omega)]
  induction m with
  | zero => simp [topMonicAmplitude]
  | succ m ih =>
    have hA := coefficientA_pos ha hb (show m+1<n+1 by omega)
    have hC := coefficientC_pos ha hb (show 0<m+1 by omega) (show m+1<n+1 by omega)
    have hL := linkProduct_pos (naturalChain_irreducible a b ha hb (n+1)) (show m<n+1 by omega)
    rw [topMonicAmplitude_succ,JacobiData.linkProduct_succ,div_pow,mul_pow,mul_pow,
      Real.sq_sqrt ((naturalChain a b ha hb (n+1)).coupling_nonneg (m+1)),
      naturalChain_coupling a b ha hb (by omega) (by omega),Nat.add_sub_cancel,
      Finset.prod_range_succ]
    rw [show topMonicAmplitude a b n m^2*(coefficientA a b (n+1) m/2)^2/
        ((naturalChain a b ha hb (n+1)).data.linkProduct m^2*
          (coefficientA a b (n+1) m*coefficientC a b (n+1) (m+1)/4))=
        (topMonicAmplitude a b n m/(naturalChain a b ha hb (n+1)).data.linkProduct m)^2*
          (coefficientA a b (n+1) m/coefficientC a b (n+1) (m+1)) by
      field_simp [hA.ne',hC.ne',hL.ne']
      ring]
    rw [ih (by omega)]

end
end jacobi.Support
