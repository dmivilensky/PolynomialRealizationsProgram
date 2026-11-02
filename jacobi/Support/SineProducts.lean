import jacobi.Support.Parameters
import chebyshev1.SineJacobi.LogSinc

/-!
Article: jacobi, Appendix C.3 (sine-product estimates).
The step is an explicit argument so the same statements also cover h/2.
Use: the actual top-node formula uses sineProduct at the original step, while the spectral-weight formula and its estimates also use the half step.
-/
namespace jacobi.Support
noncomputable section
open Real

/-- The original finite sine product at an explicitly chosen lattice step.
Use: the actual top-node formula uses sineProduct at the original step, while the spectral-weight formula and its estimates also use the half step.
Article: jacobi, Appendix C.3 (sine-product estimates).
-/
def sineProduct (h s : ℝ) (m : ℕ) : ℝ :=
  ∏ j∈Finset.range m,sin (((j:ℝ)+s)*h)/sin (((j:ℝ)+1)*h)

/-- The original empty sine product equals one.
Use: the exact top-node factorization has the original constant-polynomial normalization.
Article: jacobi, Appendix C.3 (sine-product estimates).
Proof: the actual product has no factors. -/
theorem sineProduct_zero (h s : ℝ) : sineProduct h s 0=1 := by
  simp [sineProduct]

/-- The actual sine product has its exact original next sine quotient.
Use: top-node factorization and subsequent logarithmic sine-product estimates use the same finite product.
Article: jacobi, Appendix C.3 (sine-product estimates).
Proof: split the genuine finite product at its last index. -/
theorem sineProduct_succ (h s : ℝ) (m : ℕ) :
    sineProduct h s (m+1)=sineProduct h s m*
      (sin (((m:ℝ)+s)*h)/sin (((m:ℝ)+1)*h)) :=
  Finset.prod_range_succ _ _

/-- Every actual sine product with all used arguments in the original positive sine interval is strictly positive.
Use: the exact top-node factorization divides by the genuine positive beta sine product, and logarithmic estimates use genuine positive factors.
Article: jacobi, Appendix C.3 (sine-product estimates).
Proof: each numerator and denominator is the sine of a strictly positive angle below pi. -/
theorem sineProduct_pos {h s : ℝ} {m : ℕ}
    (hnum : ∀j<m,0<((j:ℝ)+s)*h ∧ ((j:ℝ)+s)*h<π)
    (hden : ∀j<m,0<((j:ℝ)+1)*h ∧ ((j:ℝ)+1)*h<π) :
    0<sineProduct h s m := by
  apply Finset.prod_pos
  intro j hj
  have hj' := Finset.mem_range.mp hj
  exact div_pos (sin_pos_of_pos_of_lt_pi (hnum j hj').1 (hnum j hj').2)
    (sin_pos_of_pos_of_lt_pi (hden j hj').1 (hden j hj').2)

end
end jacobi.Support
