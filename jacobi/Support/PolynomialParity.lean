import jacobi.Support.ParameterReflection
import jacobi.Support.AffinePolynomials

/-!
Article: jacobi, Appendix C.3 (support weights and segment bounds).
The actual original natural and corrected support orthogonal polynomials
have the printed exact parameter-swap parity, with their genuine positive
leading-coefficient normalization retained.
Use: naturalPolynomial_parity applies the true reflected continuant identity without introducing an erroneous signed coupling normalization.
-/
namespace jacobi.Support
noncomputable section
open Real Polynomial jacobi.Finite chebyshev1 chebyshev2

/-- The actual spectral reflection retains the genuine original positive coupling product.
Use: naturalPolynomial_parity applies the true reflected continuant identity without introducing an erroneous signed coupling normalization.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: reflection multiplies every original squared coupling by (-1)^2=1, so every original square root and its finite product is unchanged. -/
theorem reflect_linkProduct {n : ℕ} (J : Jacobi n) (m : ℕ) :
    (reflect J).data.linkProduct m=J.data.linkProduct m := by
  simp [jacobi.Finite.reflect,affine,JacobiData.linkProduct]

/-- The genuine natural support polynomials have precisely the original parity under parameter swap.
Use: the left support edge and its envelopes are reduced to the actual right-edge family with the original canonical orientation.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: the actual swapped matrix is the proved spectral reflection. Its genuine coupling normalization is unchanged and its original leading continuant has the exact reflected evaluation formula. -/
theorem naturalPolynomial_parity (a b : ℝ) (ha : -1<a) (hb : -1<b)
    (n m : ℕ) (hm:m≤n+1) (x : ℝ) :
    (naturalPolynomial b a hb ha n m).eval x=
      (-1:ℝ)^m*(naturalPolynomial a b ha hb n m).eval (-x) := by
  -- Reflect the actual continuant while retaining its positive, unsigned coupling normalization.
  rw [naturalPolynomial,naturalChain_swap,normalizedLeading,Polynomial.eval_mul,
    Polynomial.eval_C,reflect_linkProduct]
  have h := leading_affine_eval (naturalChain a b ha hb (n+1))
    (by norm_num : (-1:ℝ)≠0) 0 x m hm
  simp only [sub_zero,div_neg,div_one] at h
  change ((jacobi.Finite.reflect (naturalChain a b ha hb (n+1))).data.leading m).eval x=
    (-1:ℝ)^m*((naturalChain a b ha hb (n+1)).data.leading m).eval (-x) at h
  rw [h]
  simp only [naturalPolynomial,normalizedLeading,Polynomial.eval_mul,Polynomial.eval_C]
  ring

/-- The genuine corrected support orthogonal polynomials satisfy the article's full original parameter-swap parity at every real spectral point.
Use: the alternating beta contribution in the actual two-edge Gram limit uses these exact same support polynomials.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: use the already proved actual affine polynomial identity, the exact invariance of the model scale and sign reversal of its shift, and the genuine natural polynomial parity. -/
theorem supportPolynomial_parity (a b : ℝ) (ha : -1<a) (hb : -1<b)
    (n : ℕ) (i:Fin (n+1)) (x : ℝ) :
    (supportPolynomial a b ha hb n i).eval (-x)=
      (-1:ℝ)^i.val*(supportPolynomial b a hb ha n i).eval x := by
  -- The exact affine shift sign is included, so this is parity for the genuine corrected family.
  rw [supportPolynomial_eval,supportPolynomial_eval,naturalPolynomial_parity b a hb ha n i
    (Nat.le_of_lt i.isLt)]
  obtain ⟨hc,hd⟩ := affine_swap a b (n+1)
  rw [hc,hd]
  congr 2
  ring

end
end jacobi.Support
