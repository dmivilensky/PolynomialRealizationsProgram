import jacobi.Jacobi.EquationUniqueness
import jacobi.Jacobi.Degree

/-!
Article: jacobi, Proposition C.2.
The literal shifted Jacobi polynomials reflect by exchanging their two
parameters and adjusting the endpoint normalization. The proof uses the
actual polynomial differential equation and its proved endpoint uniqueness.
Use: obtains both-edge zero statements from one edge using actual source polynomials.
-/
namespace jacobi.Jacobi
noncomputable section
open Polynomial

/-- Reflection of a genuine shifted Jacobi polynomial solves the parameter-exchanged Jacobi equation.
Use: obtains both-edge zero statements from one edge using actual source polynomials.
Article: jacobi, Proposition C.2.
Proof: the community polynomial chain rule gives the sign of the first
derivative and the unchanged second derivative. Evaluate at every real
point and use the genuine original equation at the reflected argument. -/
theorem reflected_residual {a b : ℝ} (ha : -1<a) (n : ℕ) :
    equationResidual b a n ((shiftedPolynomial a b n).comp (1-X))=0 := by
  -- Work with the literal polynomial composition; the reflected solution is not introduced axiomatically.
  apply Polynomial.funext
  intro t
  rw [equationResidual_eval]
  simp only [derivative_comp_one_sub_X,derivative_neg,eval_neg,neg_neg,
    eval_comp,eval_sub,eval_one,eval_X,eval_zero]
  have h := shiftedPolynomial_equation_eval (b := b) ha n (1-t)
  dsimp only at h
  linear_combination h

/-- The actual endpoint-normalized Jacobi polynomials have the exact parameter-reflection identity.
Use: transfers genuine zeros and all subsequent edge estimates to the opposite endpoint without an independent special-function definition.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: the reflected original polynomial and the scalar multiple of the
parameter-exchanged original polynomial solve the same actual equation.
Their endpoint values agree, so the proved triangular uniqueness theorem
identifies them as polynomials. -/
theorem shiftedPolynomial_reflection {a b : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ) :
    (shiftedPolynomial a b n).comp (1-X)=
      C ((shiftedPolynomial a b n).eval 1)*shiftedPolynomial b a n := by
  -- The scalar is the actual opposite-endpoint value, retaining the normalization of the original finite series.
  apply equation_unique hb n _ _ (reflected_residual ha n)
  · rw [equationResidual_const_mul,shiftedPolynomial_residual hb n,mul_zero]
  · simp only [eval_comp,eval_sub,eval_one,eval_X,sub_zero,eval_mul,eval_C,
      shiftedPolynomial_zero,mul_one]

/-- The two actual opposite-endpoint Jacobi values multiply to one.
Use: proves the reflection factor is nonzero in the full source parameter range, including negative endpoint exponents.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: evaluate the proved polynomial reflection at one, where the reflected original value is the genuine normalization one. -/
theorem reflection_factor_product {a b : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ) :
    (shiftedPolynomial a b n).eval 1*(shiftedPolynomial b a n).eval 1=1 := by
  have h := congrArg (fun p : Polynomial ℝ => p.eval 1) (shiftedPolynomial_reflection ha hb n)
  simpa only [eval_comp,eval_sub,eval_one,eval_X,sub_self,shiftedPolynomial_zero,eval_mul,eval_C] using h.symm

/-- The actual normalized Jacobi reflection factor never vanishes.
Use: reflection preserves the entire zero set and its finite canonical order.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: its product with the genuine reverse reflection factor is exactly one. -/
theorem reflection_factor_ne_zero {a b : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ) :
    (shiftedPolynomial a b n).eval 1≠0 := by
  intro hz
  have h := reflection_factor_product ha hb n
  rw [hz,zero_mul] at h
  norm_num at h

/-- Reflection identifies the complete actual real zero sets of the two Jacobi parameter orders.
Use: provides the rigorous both-edge symmetry used in the source's zero estimates.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: evaluate the proved reflection identity and cancel its genuinely nonzero endpoint factor. -/
theorem reflected_zero_iff {a b t : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ) :
    (shiftedPolynomial a b n).eval (1-t)=0 ↔ (shiftedPolynomial b a n).eval t=0 := by
  have h := congrArg (fun p : Polynomial ℝ => p.eval t) (shiftedPolynomial_reflection ha hb n)
  simp only [eval_comp,eval_sub,eval_one,eval_X,eval_mul,eval_C] at h
  rw [h,mul_eq_zero,or_iff_right (reflection_factor_ne_zero ha hb n)]

end
end jacobi.Jacobi
