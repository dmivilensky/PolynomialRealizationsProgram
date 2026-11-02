import jacobi.Support.PolynomialParity
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
Article: jacobi, Appendix C.3 (support weights and segment bounds).
The actual corrected orthogonal-polynomial derivative has its exact
affine scaling and its exact parameter-reflection norm. These identities
transfer the natural angular estimates and the right-half weighted bounds
to the genuine corrected polynomial on both spectral halves.
Use: supportPolynomial_segment_bounds converts the genuine natural support derivative envelope to the actual corrected support polynomial.
-/
namespace jacobi.Support
noncomputable section
open Real Polynomial

/-- The actual corrected support spectral derivative has precisely the inverse affine scale prescribed by the original coordinate change.
Use: supportPolynomial_segment_bounds converts the genuine natural support derivative envelope to the actual corrected support polynomial.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Source: the polynomial derivative and the ordinary real chain rule.
Proof: differentiate the already proved exact original affine evaluation identity. The community derivative of the same actual corrected polynomial is unique. -/
theorem supportPolynomial_derivative_eval (a b:ℝ) (ha:-1<a) (hb:-1<b)
    (n:ℕ) (i:Fin (n+1)) (x:ℝ) :
    (supportPolynomial a b ha hb n i).derivative.eval x=
      (naturalPolynomial a b ha hb n i).derivative.eval
        ((x- jacobi.Jacobi.modelShift a b (n+1))/ jacobi.Jacobi.modelScale a b (n+1))/
          jacobi.Jacobi.modelScale a b (n+1) := by
  -- Differentiate the actual evaluation formula, preserving its original normalization.
  let c := jacobi.Jacobi.modelScale a b (n+1)
  let d := jacobi.Jacobi.modelShift a b (n+1)
  let P := naturalPolynomial a b ha hb n i
  have h := (P.hasDerivAt ((x-d)/c)).comp x (((hasDerivAt_id x).sub_const d).div_const c)
  have hh : HasDerivAt (fun y => (supportPolynomial a b ha hb n i).eval y)
      (P.derivative.eval ((x-d)/c)/c) x := by
    convert h using 1
    · funext y
      exact supportPolynomial_eval a b ha hb n i y
    · simp only [one_div]
      ring
  exact ((supportPolynomial a b ha hb n i).hasDerivAt x).unique hh

/-- The actual support polynomial and its spectral derivative have unchanged absolute values under the genuine endpoint-parameter reflection.
Use: supportPolynomial_segment_bounds obtains the complete opposite-edge interpolation estimates from the already proved right-half bounds.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: the already proved original polynomial parity gives the first identity. Differentiate that same identity using the real chain rule; its only extra factor is minus one. Absolute values remove both genuine signs. -/
theorem supportPolynomial_reflected_norms (a b:ℝ) (ha:-1<a) (hb:-1<b)
    (n:ℕ) (i:Fin (n+1)) (x:ℝ) :
    |(supportPolynomial a b ha hb n i).eval (-x)|=|(supportPolynomial b a hb ha n i).eval x| ∧
    |(supportPolynomial a b ha hb n i).derivative.eval (-x)|=
      |(supportPolynomial b a hb ha n i).derivative.eval x| := by
  -- This is spectral-variable reflection, so no physical matrix-row reversal is involved.
  constructor
  · rw [supportPolynomial_parity,abs_mul,abs_pow]
    norm_num
  · let P := supportPolynomial a b ha hb n i
    let Q := supportPolynomial b a hb ha n i
    have he : (fun y:ℝ => P.eval (-y))=(fun y:ℝ => (-1:ℝ)^i.val*Q.eval y) :=
      funext (supportPolynomial_parity a b ha hb n i)
    have hl := (P.hasDerivAt (-x)).comp x (hasDerivAt_neg x)
    have hr := (Q.hasDerivAt x).const_mul ((-1:ℝ)^i.val)
    change HasDerivAt (fun y:ℝ => P.eval (-y)) (P.derivative.eval (-x)*(-1)) x at hl
    rw [he] at hl
    have h := congrArg abs (hl.unique hr)
    simpa only [abs_mul,abs_neg,abs_one,abs_pow,one_pow,mul_one,one_mul] using h

end
end jacobi.Support
