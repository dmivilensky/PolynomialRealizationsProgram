import krylov.Information.PhysicalRadius
import krylov.Reference.CanonicalGradient
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), true relative curvature control.
Use: bound every actual informed trial error by the genuine known-base
relative matrix budget, uniformly in all observed directions.
Source: canonical primal/dual pairing, Cauchy--Schwarz and the true spectral
operator norm; the physical relative budget is retained exactly. -/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix krylov.Reference krylov.Secant krylov.Information
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual relative spectral matrix budget controls every physical
curvature change in the genuine known-base energy.
Use: native informed policies have uniform relative trial-error bounds from
physical matrix priors, without trajectory or direction regularity hypotheses.
Article: main_krylov, thm:local(a).
Proof: the exact primal/dual metric dictionary turns the physical quadratic
form into the true normalized operator action. Cauchy--Schwarz and its
spectral norm give the bound, with the actual root energy as denominator. -/
theorem relative_curvature_bound (known change : Matrix (Fin n) (Fin n) ℝ)
    (hknown : known.PosDef) (d : EuclideanSpace ℝ (Fin n)) :
    |inner ℝ d (cgOperator change d)|≤relativeBudget known change*inner ℝ d (cgOperator known d) := by
  let x := cgOperator (metricRoot known) d
  let T := cgOperator (relativeOperator known change)
  have he : inner ℝ d (cgOperator change d)=inner ℝ x (T x) := by
    rw [canonical_search_pairing known hknown]
    exact congrArg (inner ℝ x) (canonical_form_action known change hknown d).symm
  have henergy : inner ℝ d (cgOperator known d)=‖x‖^2 := by
    rw [canonical_search_pairing known hknown,canonical_reference_action known hknown,real_inner_self_eq_norm_sq]
    rfl
  have hnorm : ‖T‖=relativeBudget known change := by
    exact (Matrix.l2_opNorm_toEuclideanCLM _).symm
  rw [he,henergy,← hnorm]
  calc
    _ ≤ ‖x‖*‖T x‖ := abs_real_inner_le_norm x (T x)
    _ ≤ ‖x‖*(‖T‖*‖x‖) := mul_le_mul_of_nonneg_left (T.le_opNorm x) (norm_nonneg x)
    _ = _ := by ring

/-- Dividing the actual curvature change by positive known curvature
retains the exact physical relative budget bound.
Use: this is the source informed relative-error estimate at every active step.
Article: main_krylov, thm:local(a).
Proof: known positive definiteness gives the genuine nonzero energy; divide
the already proved physical quadratic-form bound by that same true energy. -/
theorem relative_curvature_quotient_bound (known change : Matrix (Fin n) (Fin n) ℝ)
    (hknown : known.PosDef) (d : EuclideanSpace ℝ (Fin n)) (hd : d≠0) :
    |(-inner ℝ d (cgOperator change d))/inner ℝ d (cgOperator known d)|≤relativeBudget known change := by
  have hp := (cgOperator_positive known hknown).2 d hd
  rw [abs_div,abs_neg,abs_of_pos hp]
  exact (div_le_iff₀ hp).mpr (relative_curvature_bound known change hknown d)

end
end krylov.LinearAlgebra
