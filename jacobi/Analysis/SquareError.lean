import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
Article: jacobi, Theorem C.5.
The exact square and squared-norm error estimates needed for the two
different complex shifted energies. These are kept distinct because
squaring the complex value and squaring its modulus are different limits.
Source: the difference of squares and the reverse triangle inequality.
Use: finiteShiftedSquare_uniform and Theorem C.5's complex energy.
-/
namespace jacobi.Analysis
noncomputable section

/-- The original complex square difference is controlled by the true
value error times the sum of the two original norms.
Use: finiteShiftedSquare_uniform and Theorem C.5's complex energy.
Article: jacobi, Theorem C.5.
Proof: factor the exact difference of squares and use the norm triangle. -/
theorem complex_square_error (z w:ℂ) :
    ‖z^2-w^2‖≤‖z-w‖*(‖z‖+‖w‖) := by
  rw [show z^2-w^2=(z-w)*(z+w) by ring,norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_add_le z w) (norm_nonneg _)

/-- The original squared-norm difference is controlled by the same
actual value error times the sum of the two genuine norms.
Use: finiteShiftedNormSquare_uniform and Theorem C.5's modulus-squared energy.
Article: jacobi, Theorem C.5.
Proof: factor the scalar norm squares and use the reverse triangle inequality. -/
theorem norm_square_error {E:Type*} [SeminormedAddCommGroup E] (z w:E) :
    |‖z‖^2-‖w‖^2|≤‖z-w‖*(‖z‖+‖w‖) := by
  rw [show ‖z‖^2-‖w‖^2=(‖z‖-‖w‖)*(‖z‖+‖w‖) by ring,abs_mul,
    abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le z w) (by positivity)

end
end jacobi.Analysis
