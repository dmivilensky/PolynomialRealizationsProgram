import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Article: main_krylov, thm:RFCS, genuine gradient-to-error cubic comparison.
Use: Preserve the exact leading gradient coefficient when passing to the
actual local error norm after a true small relative gradient-error bound.
Source: the norm triangle inequality and an explicit scalar absorption.
-/

namespace krylov.Nonlinear
variable {E : Type*} [NormedAddCommGroup E]

/-- A genuine small relative gradient/error mismatch and quadratic gradient bound change the actual error estimate by only the displayed cubic remainder.
Use: Retain the original last-probe leading coefficient in the final nonlinear error norm.
Article: main_krylov, thm:RFCS, actual leading-coefficient preserving error transfer.
Proof: Absorb the true relative mismatch to bound the actual error by twice the gradient norm, then insert the genuine quadratic gradient bound back into that mismatch.
-/
theorem norm_error_le_gradient_add_cubic (x g : E) {a b ε : ℝ}
    (ha : 0≤a) (hε : 0≤ε) (hsmall : a*ε≤1/2)
    (hdiff : ‖x-g‖≤a*ε*‖x‖) (hg : ‖g‖≤b*ε^2) :
    ‖x‖≤‖g‖+2*a*b*ε^3 := by
  have hn : ‖x‖≤‖g‖+‖x-g‖ := by
    calc
      _ = ‖(x-g)+g‖ := by rw [sub_add_cancel]
      _ ≤ ‖x-g‖+‖g‖ := norm_add_le _ _
      _ = _ := add_comm _ _
  have htwo : ‖x‖≤2*‖g‖ := by
    have hprod := mul_le_mul_of_nonneg_right hsmall (norm_nonneg x)
    linarith
  have hbound : ‖x-g‖≤2*a*b*ε^3 := by
    calc
      _ ≤ a*ε*‖x‖ := hdiff
      _ ≤ a*ε*(2*‖g‖) := mul_le_mul_of_nonneg_left htwo (mul_nonneg ha hε)
      _ ≤ a*ε*(2*(b*ε^2)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg (by norm_num)) (mul_nonneg ha hε)
      _ = _ := by ring
  exact hn.trans (add_le_add le_rfl hbound)

end krylov.Nonlinear
