import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
A weighted product of two actual polynomials has its genuine mean-value
bound on the whole interval between its two spectral arguments. This
elementary estimate turns the proved support-weight bounds of Appendix C.3
into the actual original target-minus-support Gram summand estimate.
Source: the ordinary mean-value inequality and the product rule.
Use: supportGram_node_change applies this bound to the original corrected support polynomials and their genuine target-to-support node segment in the proof of Appendix C.4.
-/
namespace jacobi.Finite
noncomputable section
open Real Set Polynomial

/-- A genuine weighted polynomial product has the full spectral-segment Lipschitz bound supplied by the weighted value and derivative estimates of its two factors.
Use: supportGram_node_change applies this bound to the original corrected support polynomials and their genuine target-to-support node segment in the proof of Appendix C.4.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Source: mean-value inequality, mathlib Convex.norm_image_sub_le_of_norm_deriv_le.
Proof: differentiate the actual weighted product. Write its derivative as the sum of the two products of sqrt(w)-weighted factors, using sqrt(w)^2=w. The four assumed interval bounds give 2*C*D for its derivative. Apply the community mean-value inequality on the complete convex interval joining the two original spectral arguments. -/
theorem weighted_polynomial_product_change (p q:ℝ[X]) {w C D x y:ℝ}
    (hw:0≤w) (hC:0≤C) (hD:0≤D)
    (hp:∀t∈uIcc x y,sqrt w*|p.eval t|≤C ∧ sqrt w*|p.derivative.eval t|≤D)
    (hq:∀t∈uIcc x y,sqrt w*|q.eval t|≤C ∧ sqrt w*|q.derivative.eval t|≤D) :
    w*|p.eval y*q.eval y-p.eval x*q.eval x|≤2*C*D*|y-x| := by
  -- The interval derivative is that of the same original weighted product at both actual endpoints.
  let r := sqrt w
  let g (t:ℝ) := w*(p.eval t*q.eval t)
  have hr : 0≤r := sqrt_nonneg w
  have hrw : r^2=w := sq_sqrt hw
  have hd (t:ℝ) : HasDerivAt g (w*(p.derivative.eval t*q.eval t+p.eval t*q.derivative.eval t)) t :=
    ((p.hasDerivAt t).mul (q.hasDerivAt t)).const_mul w
  have hderiv (t:ℝ) (ht:t∈uIcc x y) : ‖deriv g t‖≤2*C*D := by
    rw [(hd t).deriv,Real.norm_eq_abs]
    have he : w*(p.derivative.eval t*q.eval t+p.eval t*q.derivative.eval t)=
        (r*p.derivative.eval t)*(r*q.eval t)+(r*p.eval t)*(r*q.derivative.eval t) := by rw [← hrw]; ring
    rw [he]
    have hvp : |r*p.eval t|≤C := by rw [abs_mul,abs_of_nonneg hr]; exact (hp t ht).1
    have hdp : |r*p.derivative.eval t|≤D := by rw [abs_mul,abs_of_nonneg hr]; exact (hp t ht).2
    have hvq : |r*q.eval t|≤C := by rw [abs_mul,abs_of_nonneg hr]; exact (hq t ht).1
    have hdq : |r*q.derivative.eval t|≤D := by rw [abs_mul,abs_of_nonneg hr]; exact (hq t ht).2
    calc
      _ ≤ |(r*p.derivative.eval t)*(r*q.eval t)|+|(r*p.eval t)*(r*q.derivative.eval t)| := abs_add_le _ _
      _ = |r*p.derivative.eval t| * |r*q.eval t|+|r*p.eval t| * |r*q.derivative.eval t| := by simp only [abs_mul]
      _ ≤ D*C+C*D := add_le_add (mul_le_mul hdp hvq (abs_nonneg _) hD) (mul_le_mul hvp hdq (abs_nonneg _) hC)
      _ = _ := by ring
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜:=ℝ)
    (fun t (_:t∈uIcc x y) => (hd t).differentiableAt) hderiv (convex_uIcc x y) left_mem_uIcc right_mem_uIcc
  have he : g y-g x=w*(p.eval y*q.eval y-p.eval x*q.eval x) := by dsimp [g]; ring
  rw [he,Real.norm_eq_abs,abs_mul,abs_of_nonneg hw,Real.norm_eq_abs] at hh
  exact hh

end
end jacobi.Finite
