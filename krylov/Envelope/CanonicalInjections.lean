import krylov.Envelope.CanonicalFiltration
import krylov.Stability.CanonicalDirectionGeometry
import krylov.Variation.FCResponse

set_option autoImplicit false
/-!
Article: main_krylov, thm:E and s3:def:phi, genuine canonical source injections.
Use: transport actual polynomial frozen responses through the true metric
root and identify their real primitive segment-derivative injections with
the printed canonical increments acting on genuine computed CG steps.
Source: standard commuting polynomial functional calculus, actual
positive-root cancellations and the true constructed canonical affine path.
-/

namespace krylov.Envelope
noncomputable section
open Matrix Polynomial krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation
open scoped BigOperators Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- Every true commuting linear map commutes with actual polynomial evaluation on genuine vectors.
Use: Every true commuting linear map commutes with actual polynomial evaluation on genuine vectors.
Article: main_krylov, thm:E and s3:def:phi, genuine canonical source injections.
Proof: Expand the actual polynomial into its real finite power sum; true power commutation and genuine linearity preserve each actual coefficient action. -/
theorem polynomial_action_commute (T Q : E →ₗ[ℝ] E) (h : Commute T Q) (p : ℝ[X]) (v : E) :
    T (aeval Q p v)=aeval Q p (T v) := by
  rw [Polynomial.aeval_eq_sum_range]
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro i _
  have he := LinearMap.congr_fun (h.pow_right i).eq v
  exact congrArg (fun w => p.coeff i • w) he

/-- The genuine inverse metric root commutes with every actual polynomial of the true reference operator.
Use: The genuine inverse metric root commutes with every actual polynomial of the true reference operator.
Article: main_krylov, thm:E and s3:def:phi, genuine canonical source injections.
Proof: Actual primal/dual root identities show true root/reference commutation; apply the proved genuine commuting polynomial action theorem. -/
theorem canonical_polynomial_action (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (p : ℝ[X]) (v : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ (aeval (cgOperator base).toLinearMap p v)=
      aeval (cgOperator base).toLinearMap p (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ v) := by
  -- The real inverse-root/reference products both equal the genuine primal root, giving true operator commutation.
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
  have hc : Commute R.toLinearMap (cgOperator base).toLinearMap := by
    apply LinearMap.ext
    intro w
    change R (cgOperator base w)=cgOperator base (R w)
    dsimp only [R]
    rw [canonical_reference_action base hb,canonical_base_dual base hb]
  exact polynomial_action_commute R.toLinearMap (cgOperator base).toLinearMap hc p v

/-- The true inverse-root image of an actual physical canonical drift action equals the genuine canonical increment acting on the real root image.
Use: The true inverse-root image of an actual physical canonical drift action equals the genuine canonical increment acting on the real root image.
Article: main_krylov, thm:E and s3:def:phi, genuine canonical source injections.
Proof: Cancel the actual nonsingular positive root in the genuine matrix product before applying the real Euclidean operator map. -/
theorem canonical_drift_action (base C : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (v : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base*C*metricRoot base) v)=
        Matrix.toEuclideanCLM (𝕜 := ℝ) C (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) v) := by
  have he : (metricRoot base)⁻¹*(metricRoot base*C*metricRoot base)=C*metricRoot base := by
    rw [← Matrix.mul_assoc,← Matrix.mul_assoc,nonsing_inv_mul _ (metricRoot_det_unit base hb),Matrix.one_mul]
  rw [← mul_apply_eq_comp,← map_mul,he,map_mul,mul_apply_eq_comp]

/-- Every genuine physical reference-step injection of the actual canonical source path normalizes to the true cumulative canonical increments acting on the real computed CG step.
Use: Every genuine physical reference-step injection of the actual canonical source path normalizes to the true cumulative canonical increments acting on the real computed CG step.
Article: main_krylov, thm:E and s3:def:phi, genuine canonical source injections.
Proof: Differentiate the genuine constructed affine segment path and use the proved actual canonical drift action identity. -/
theorem referenceInjection_canonicalPath (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (i : ℕ) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
      (referenceInjection (cgOperator base) g (canonicalFCPath base E) (i+1))=
      Matrix.toEuclideanCLM (𝕜 := ℝ) (∑ l∈Finset.range i, E l) (canonicalCGStep base g i) := by
  rw [referenceInjection,(canonicalFCPath_calculus base E i).2.deriv]
  exact canonical_drift_action base _ hb _
end
end krylov.Envelope
