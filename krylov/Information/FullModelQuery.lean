import krylov.Information.PreQuadraticModel
import krylov.Methods.RFCPhase
import krylov.Secant.Correction


/-!
Article: main_krylov, s4:cor-Q, actual centred physical RFC solve.
Use: prove the true final gate, correction query, returned gradient and
common-twin information radius for the original pre-quadratic source.
Source: genuine CG prefix shadow, exact square physical model solve and
the proved actual common-centre reflection and robust two-scenario radius.
-/

namespace krylov.Information
noncomputable section
open Matrix Finset krylov.Reference krylov.Methods krylov.Secant krylov.Correction krylov.Stability krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n N : ℕ}

/-- A genuine physical full-column combination is exactly the Euclidean action of its true column matrix.
Use: Connect real correction queries to the already proved physical matrix solve.
Article: main_krylov, s4:cor-Q, genuine centred RFC execution.
Proof: Evaluate both true finite column sums and commute the real scalar factor. -/
theorem combine_fullBasisMatrix (u : Fin n → EuclideanSpace ℝ (Fin n)) (c : Fin n → ℝ) :
    combine u c=cgOperator (fullBasisMatrix u) (WithLp.toLp 2 c) := by
  ext i
  change (∑ j, c j • u j) i=((fullBasisMatrix u)*ᵥc) i
  simp only [WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul,Matrix.mulVec,dotProduct,
    fullBasisMatrix,Matrix.of_apply]
  exact sum_congr rfl (fun _ _ => mul_comm _ _)

/-- The actual full coefficient-model correction query is exactly minus the genuine inverse physical model applied to the actual incoming gradient.
Use: Identify a real executed physical query with the common-centre solve.
Article: main_krylov, s4:cor-Q, genuine centred RFC execution.
Proof: True full-basis projection identifies the actual right-hand side. Reuse the proved square physical correction theorem and its genuine full-column inverse domain. -/
theorem full_model_query (u : Fin n → EuclideanSpace ℝ (Fin n))
    (H : Matrix (Fin n) (Fin n) ℝ) (hu : IsUnit (fullBasisMatrix u).det)
    (g : EuclideanSpace ℝ (Fin n)) :
    combine u (modelCoefficients u H g)=-(cgOperator (inverseCongruence (fullBasisMatrix u) H)⁻¹ g) := by
  -- The actual projected right-hand side is the true full-column transpose action.
  have hp : coordinates u g=(fullBasisMatrix u)ᵀ*ᵥ(WithLp.ofLp g) := by
    exact congrArg (WithLp.ofLp) (projectedResidual_fullBasisMatrix u g)
  rw [combine_fullBasisMatrix,modelCoefficients,hp]
  apply (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).injective
  change fullBasisMatrix u*ᵥ(-(H⁻¹*ᵥ((fullBasisMatrix u)ᵀ*ᵥWithLp.ofLp g)))=
    -((inverseCongruence (fullBasisMatrix u) H)⁻¹*ᵥWithLp.ofLp g)
  simpa only [correctionCoefficients,Matrix.neg_mulVec] using
    square_correction_step (fullBasisMatrix u) H hu (WithLp.ofLp g)

end
end krylov.Information
