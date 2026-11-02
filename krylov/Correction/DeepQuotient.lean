import krylov.Correction.DeepExecution

/-!
Article: main_krylov, prop:deep, actual terminal adjugate residual identity.
Use: Identify the true final RFC source output as the post-search gradient
minus its genuine physical adjugate numerator divided by its model determinant.
Source: standard matrix inverse/adjugate identity (mathlib Matrix.inv_def),
finite linear synthesis and the original independently probed correction.
-/

namespace krylov.Correction.Certificate
noncomputable section
open Matrix Finset chebyshev2.Numerics.IntegerCertificate krylov.Methods
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

/-- The genuine finite original model correction equals its actual adjugate numerator times the true determinant reciprocal.
Use: Expose the genuine original RFC singular-model residual mechanism.
Article: main_krylov, prop:deep, actual original terminal quotient.
Proof: Use the standard totalized matrix inverse identity, linear finite synthesis and the true physical correction operator.
-/
theorem modelCorrection_adjugate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → EuclideanSpace ℝ (Fin 4)) (H : Matrix ι ι ℝ) (g : EuclideanSpace ℝ (Fin 4)) :
    combine s (modelCoefficients s H g)=-(H.det⁻¹ • combine s (H.adjugate*ᵥcoordinates s g)) := by
  simp only [modelCoefficients,Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_mulVec,
    combine,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,Finset.smul_sum,mul_smul,neg_smul,Finset.sum_neg_distrib]

/-- The actual terminal original source arithmetic gradient has precisely the printed physical determinant-quotient residual formula.
Use: Expose the genuine original RFC singular-model residual mechanism.
Article: main_krylov, prop:deep, actual original terminal quotient.
Proof: Use the standard totalized matrix inverse identity, linear finite synthesis and the true physical correction operator.
-/
theorem source_phase_last_quotient (x : ℕ → ℝ) :
    euclideanValue ((sourceInputPrefix 3).advance (sourceProbe 3) (sourceCorrection 3)).gradient x=
      euclideanValue (sourcePost 3) x-
        ((termDet (sourceModel 3)).value x)⁻¹ • euclideanValue sourceNumerator x := by
  -- Keep the original physical correction operator outside the genuine coefficient inverse, then use the actual determinant/adjugate factorization.
  change euclideanValue (termPhaseGradient _ _ _ _ _ _) x=_
  rw [termPhaseGradient,euclideanValue_add,euclideanValue_matVec]
  rw [termPhaseQuery,ite_eq_right (by decide : ¬3=0),termModelQuery_value,modelCorrection_adjugate]
  change euclideanValue (sourcePost 3) x+
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (matrixValue (sourceCorrection 3) x))
      (-((matrixValue (sourceModel 3) x).det⁻¹ • combine
        (fun i => euclideanValue (sourceAugSteps 3 i) x)
        ((matrixValue (sourceModel 3) x).adjugate*ᵥ
          coordinates (fun i => euclideanValue (sourceAugSteps 3 i) x) (euclideanValue (sourcePost 3) x))))=_
  rw [map_neg,map_smul]
  have hn : euclideanValue sourceNumerator x=
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (matrixValue (sourceCorrection 3) x))
        (combine (fun i => euclideanValue (sourceAugSteps 3 i) x)
          ((matrixValue (sourceModel 3) x).adjugate*ᵥ
            coordinates (fun i => euclideanValue (sourceAugSteps 3 i) x) (euclideanValue (sourcePost 3) x))) := by
    rw [sourceNumerator,euclideanValue_matVec,termCombine_value,termMatVec_value,termAdj_value,termCoordinates_value]
  rw [hn,termDet_value,sub_eq_add_neg]

end
end krylov.Correction.Certificate
