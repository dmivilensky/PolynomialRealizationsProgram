import krylov.Correction.GatedUniformRecording

/-!
Article: main_krylov, thm:UCq, true quadratic recorded-pair contamination.
Use: Turn the genuine small relative correction estimate into the original
second-order relative secant inconsistency, keeping real measured gradients.
Source: the actual probed secant balance, exact canonical metric transport
and quantitative norm noncancellation of line-plus-correction displacements.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- A true correction no larger than half its actual line has a controlled ratio to the total recorded displacement.
Use: Assemble the genuine uniform RFC second-order response from actual observations.
Article: main_krylov, thm:UCq.
Proof: The actual line norm is bounded by the recorded norm plus the correction norm. Absorb the latter with the genuine one-half allowance.
-/
theorem correction_line_to_recorded_bound (line χ : E) {q : ℝ} (hq : 0≤q) (hqhalf : q≤1/2)
    (hχ : ‖χ‖≤q*‖line‖) : ‖χ‖≤2*q*‖line+χ‖ := by
  have ht := norm_sub_le (line+χ) χ
  rw [add_sub_cancel_right] at ht
  have hm := mul_le_mul_of_nonneg_left ht hq
  have hh := mul_le_mul_of_nonneg_right hqhalf (norm_nonneg χ)
  nlinarith only [hχ,hm,hh]

variable {n : ℕ}

/-- The genuine measured canonical secant differs from its actual line-operator image by exactly the independent correction-operator mismatch on the real correction.
Use: Assemble the genuine uniform RFC second-order response from actual observations.
Article: main_krylov, thm:UCq.
Proof: Apply the actual inverse-root map to the original executed secant defect identity and use genuine primal/dual operator covariance.
-/
theorem probed_canonical_contamination_identity (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (i : ℕ) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ (probedSecant m A B g i)-
      canonicalOperator base (A i) (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (probedStep m A B g i))=
      (canonicalOperator base (B i)-canonicalOperator base (A i))
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (probedPhase m A B g i).movement) := by
  have ht := congrArg (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹)
    (probedSecant_defect_identity m A B g i)
  rw [_root_.sub_apply,map_sub,map_sub] at ht
  rw [canonicalOperator_primal base hb,_root_.sub_apply,
    canonicalOperator_primal base hb,canonicalOperator_primal base hb]
  exact ht

/-- A true first-order correction-to-recorded-step allowance gives second-order relative contamination of the actual measured secant.
Use: Assemble the genuine uniform RFC second-order response from actual observations.
Article: main_krylov, thm:UCq.
Proof: The original two canonical operator budgets bound their actual mismatch by twice the perturbation scale. Apply its real operator norm to the genuine correction and use the proved exact contamination identity.
-/
theorem probed_canonical_contamination_bound (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (i : ℕ) {ε K : ℝ} (hε : 0≤ε)
    (hA : ‖canonicalOperator base (A i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε)
    (hB : ‖canonicalOperator base (B i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε)
    (hχ : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (probedPhase m A B g i).movement‖≤
      K*ε*‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (probedStep m A B g i)‖) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ (probedSecant m A B g i)-
      canonicalOperator base (A i) (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (probedStep m A B g i))‖≤
      (2*K)*ε^2*‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (probedStep m A B g i)‖ := by
  let C := canonicalOperator base (A i)
  let D := canonicalOperator base (B i)
  have hdiff : ‖D-C‖≤2*ε := by
    rw [show D-C=(D-ContinuousLinearMap.id ℝ _)-(C-ContinuousLinearMap.id ℝ _) by abel]
    exact (norm_sub_le _ _).trans ((add_le_add hB hA).trans_eq (by ring))
  rw [probed_canonical_contamination_identity base hb]
  apply ((D-C).le_opNorm _).trans
  calc
    _ ≤ (2*ε)*(K*ε*‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (probedStep m A B g i)‖) := by gcongr
    _ = _ := by ring

end
end krylov.Correction
