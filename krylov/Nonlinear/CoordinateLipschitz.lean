import krylov.Nonlinear.CanonicalAverages

/-!
Article: main_krylov, thm:RFCS, actual physical/canonical Hessian control.
Use: Reconstruct the original derivative from its genuine canonical
congruence and transfer actual canonical Lipschitz constants back to the
physical coordinates needed by the unchanged nonlinear executor.
Source: exact continuous linear inverse identities and genuine operator
composition norm bounds. Metric-coordinate maps are constructed separately.
-/

namespace krylov.Nonlinear
noncomputable section
open Set
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The genuine inverse-coordinate derivative congruence reconstructs the original actual derivative exactly.
Use: Relate actual canonical Hessian estimates to the original physical function.
Article: main_krylov, thm:RFCS, true physical/canonical derivative norm control.
Proof: Cancel the true continuous linear coordinate equivalence and its inverse on both sides of the actual derivative action.
-/
theorem coordinateDerivative_reconstruct (T : E ≃L[ℝ] E) (H : E → E →L[ℝ] E) (x : E) :
    coordinateCongruence T.symm (coordinateDerivative T H (T x))=H x := by
  apply ContinuousLinearMap.ext
  intro v
  change T (T.symm (H (T.symm (T x)) (T.symm (T v))))=H x v
  rw [T.symm_apply_apply,T.symm_apply_apply,T.apply_symm_apply]

/-- A genuine inverse-coordinate operator congruence is bounded by the square of the actual inverse coordinate operator norm.
Use: Track only fixed metric constants in the nonlinear remainder while preserving the sharp canonical leading coefficient.
Article: main_krylov, thm:RFCS, true physical/canonical derivative norm control.
Proof: Apply the true continuous-linear composition norm bound twice.
-/
theorem coordinateCongruence_norm_le (T : E ≃L[ℝ] E) (A : E →L[ℝ] E) :
    ‖coordinateCongruence T A‖≤‖T.symm.toContinuousLinearMap‖^2*‖A‖ := by
  change ‖T.symm.toContinuousLinearMap.comp (A.comp T.symm.toContinuousLinearMap)‖≤_
  calc
    _ ≤ ‖T.symm.toContinuousLinearMap‖*‖A.comp T.symm.toContinuousLinearMap‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖T.symm.toContinuousLinearMap‖*(‖A‖*‖T.symm.toContinuousLinearMap‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ = _ := by ring

/-- A genuine canonical derivative Lipschitz bound gives an actual physical derivative Lipschitz bound with the cube of the true forward coordinate operator norm.
Use: Derive the physical local Hessian constant needed by the original nonlinear source theorems from actual canonical self-concordant control.
Article: main_krylov, thm:RFCS, true physical/canonical derivative norm control.
Proof: Reconstruct the original difference by exact congruence, bound both outer physical coordinate maps and then bound the actual transformed input distance.
-/
theorem coordinateDerivative_lipschitz_pullback (T : E ≃L[ℝ] E) (H : E → E →L[ℝ] E)
    {S : Set E} {L : ℝ≥0} (hH : LipschitzOnWith L (coordinateDerivative T H) S) :
    LipschitzOnWith (‖T.toContinuousLinearMap‖₊^3*L) H (T ⁻¹' S) := by
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro x hx y hy
  have he : H x-H y=coordinateCongruence T.symm (coordinateDerivative T H (T x)-coordinateDerivative T H (T y)) := by
    rw [map_sub,coordinateDerivative_reconstruct,coordinateDerivative_reconstruct]
  have hp := hH.norm_sub_le hx hy
  have ht : ‖T x-T y‖≤‖T.toContinuousLinearMap‖*‖x-y‖ := by
    simpa only [map_sub,ContinuousLinearEquiv.coe_coe] using T.toContinuousLinearMap.le_opNorm (x-y)
  calc
    _ = ‖coordinateCongruence T.symm (coordinateDerivative T H (T x)-coordinateDerivative T H (T y))‖ := congrArg norm he
    _ ≤ ‖T.toContinuousLinearMap‖^2*‖coordinateDerivative T H (T x)-coordinateDerivative T H (T y)‖ := by
      simpa only [ContinuousLinearEquiv.symm_symm] using coordinateCongruence_norm_le T.symm _
    _ ≤ ‖T.toContinuousLinearMap‖^2*((L : ℝ)*‖T x-T y‖) := mul_le_mul_of_nonneg_left hp (sq_nonneg _)
    _ ≤ ‖T.toContinuousLinearMap‖^2*((L : ℝ)*(‖T.toContinuousLinearMap‖*‖x-y‖)) := by gcongr
    _ = _ := by simp only [NNReal.coe_mul,NNReal.coe_pow,coe_nnnorm]; ring

end
end krylov.Nonlinear
