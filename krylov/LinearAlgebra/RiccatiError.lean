import Mathlib.Tactic
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(c), genuine stable-pivot error estimate.
Use: bound the actual original Jacobi pivot error by its true contraction factor and genuine diagonal and edge coefficient defects.
Source: exact real Riccati error identity and actual positive inverse-domain bounds.
-/

namespace krylov.LinearAlgebra
noncomputable section

/-- The true positive-pivot Riccati error has its actual contractive previous-error term plus the genuine coefficient defects.
Use: The true positive-pivot Riccati error has its actual contractive previous-error term plus the genuine coefficient defects.
Article: main_krylov, prop:phi(c), genuine stable-pivot error estimate.
Proof: Expand the original exact scalar recurrence about its true fixed pivot, then use genuine positive denominator and absolute-value inequalities. -/
theorem positive_riccati_error_bound (a b B D x mu r : ℝ)
    (hD : 0 < D) (hmu : 0 < mu) (hx : mu≤x) (hcoef : B^2/(D*x)≤r) :
    |a-b^2/x-D|≤r*|x-D|+|a-(D+B^2/D)|+|b^2-B^2|/mu := by
  -- Establish the actual inverse domain before decomposing the genuine Riccati error.
  have hxpos : 0 < x := hmu.trans_le hx
  have ht : 0≤B^2/(D*x) := div_nonneg (sq_nonneg B) (mul_pos hD hxpos).le
  have he : a-b^2/x-D=(a-(D+B^2/D))-(b^2-B^2)/x+(B^2/(D*x))*(x-D) := by
    field_simp
    ring
  rw [he]
  have hdiv : |b^2-B^2|/x≤|b^2-B^2|/mu :=
    div_le_div_of_nonneg_left (abs_nonneg _) hmu hx
  have hmul := mul_le_mul_of_nonneg_right hcoef (abs_nonneg (x-D))
  -- Keep the actual diagonal and squared-edge defects separate from the true previous-pivot contraction.
  calc
    _ ≤ |a-(D+B^2/D)|+|(b^2-B^2)/x|+|(B^2/(D*x))*(x-D)| :=
      (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ = |a-(D+B^2/D)|+|b^2-B^2|/x+(B^2/(D*x))*|x-D| := by
      rw [abs_div,abs_of_pos hxpos,abs_mul,abs_of_nonneg ht]
    _ ≤ |a-(D+B^2/D)|+|b^2-B^2|/mu+r*|x-D| := by linarith
    _ = _ := by ring
end
end krylov.LinearAlgebra
