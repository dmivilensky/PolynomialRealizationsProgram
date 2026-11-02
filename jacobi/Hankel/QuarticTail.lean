import jacobi.Hankel.Potential

/-!
Article: jacobi, Lemma E.1.
These analytic identities supply the uniform cubic outgoing Hankel
remainder from the actual fourth-order polynomial ODE residual.
Use: the actual Hankel polynomial residual is a complex constant times this original integrable tail.
-/
namespace jacobi.Hankel
noncomputable section
open Set MeasureTheory

/-- The true inverse fourth power is integrable on every positive real outgoing ray.
Use: the actual Hankel polynomial residual is a complex constant times this original integrable tail.
Article: jacobi, Lemma E.1.
Proof: identify the reciprocal integer power with the community real-power improper integral of exponent minus four. -/
theorem quarticTail_integrable {x : ℝ} (hx : 0<x) :
    IntegrableOn (fun y : ℝ => y⁻¹^4) (Ioi x) := by
  simpa only [Real.rpow_neg_eq_inv_rpow,Real.rpow_ofNat] using
    integrableOn_Ioi_rpow_of_lt (by norm_num : (-4:ℝ)< -1) hx

/-- The actual fourth-order inverse-power tail has precisely the original cubic integral 1/(3*x^3).
Use: residualIntegral_bound evaluates the genuine outgoing residual majorant, so the cubic Jost error has no unevaluated tail estimate premise.
Article: jacobi, Lemma E.1.
Proof: evaluate the actual community improper-power integral at exponent minus four and simplify its original reciprocal powers. -/
theorem quarticTail_integral {x : ℝ} (hx : 0<x) :
    (∫ y in Ioi x,y⁻¹^4)=1/(3*x^3) := by
  have h := integral_Ioi_rpow_of_lt (by norm_num : (-4:ℝ)< -1) hx
  norm_num only [Real.rpow_neg_eq_inv_rpow,Real.rpow_ofNat] at h
  rw [h]
  ring

end
end jacobi.Hankel
