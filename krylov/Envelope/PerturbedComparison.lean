import krylov.Envelope.Geometry

set_option autoImplicit false
/-!
Article: main_krylov, cor:lm, comparison of actual orthogonal envelopes with remainders.
Use: retain both actual trajectory Taylor remainders in the true uniform
and quadratic-before-exhaustion norm comparison inequalities.
Source: real reverse triangle inequality and the proved exact
orthogonal-envelope comparison geometry.
-/

namespace krylov.Envelope
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
/-- Two actual vector remainder terms change a common-base norm comparison by at most the sum of their norms.
Use: Two actual vector remainder terms change a common-base norm comparison by at most the sum of their norms.
Article: main_krylov, cor:lm, comparison of actual orthogonal envelopes with remainders.
Proof: Split the actual norm difference into three genuine scalar differences and apply the real triangle and reverse triangle inequalities. -/
theorem norm_comparison_remainders (u v w r s : E) :
    |‖u+v+r‖-‖u+w+s‖|≤|‖u+v‖-‖u+w‖|+‖r‖+‖s‖ := by
  -- Isolate both true vector remainders before applying the genuine scalar triangle comparison.
  calc
    _ = |(‖u+v+r‖-‖u+v‖)+(‖u+v‖-‖u+w‖)+(‖u+w‖-‖u+w+s‖)| := by congr 1;ring
    _ ≤ |‖u+v+r‖-‖u+v‖|+|‖u+v‖-‖u+w‖|+|‖u+w‖-‖u+w+s‖| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ ‖r‖+|‖u+v‖-‖u+w‖|+‖s‖ := by
      apply add_le_add
      · exact add_le_add (by simpa only [add_sub_cancel_left] using abs_norm_sub_norm_le (u+v+r) (u+v)) le_rfl
      · simpa only [add_sub_cancel_left,abs_sub_comm] using abs_norm_sub_norm_le (u+w+s) (u+w)
    _ = _ := by ring

/-- The genuine common-envelope comparison bounds retain both actual vector remainders, uniformly and with the real quadratic denominator when positive.
Use: The genuine common-envelope comparison bounds retain both actual vector remainders, uniformly and with the real quadratic denominator when positive.
Article: main_krylov, cor:lm, comparison of actual orthogonal envelopes with remainders.
Proof: Apply the proved exact orthogonal norm comparisons, then add the true reverse-triangle remainder bounds. -/
theorem perturbed_orthogonal_comparison (u v w r s : E) (huv : inner ℝ u v=0)
    (huw : inner ℝ u w=0) :
    |‖u+v+r‖-‖u+w+s‖|≤max ‖v‖ ‖w‖+‖r‖+‖s‖ ∧
    (0<‖u‖ → |‖u+v+r‖-‖u+w+s‖|≤(‖v‖^2+‖w‖^2)/(2*‖u‖)+‖r‖+‖s‖) := by
  constructor
  · exact (norm_comparison_remainders u v w r s).trans
      (add_le_add (add_le_add (orthogonal_norm_comparison u v w huv huw) le_rfl) le_rfl)
  · intro hu
    exact (norm_comparison_remainders u v w r s).trans
      (add_le_add (add_le_add (orthogonal_norm_comparison_quadratic u v w hu huv huw) le_rfl) le_rfl)
end
end krylov.Envelope
