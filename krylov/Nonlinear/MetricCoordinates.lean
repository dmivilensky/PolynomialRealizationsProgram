import krylov.Nonlinear.CanonicalAverages
import krylov.Reference.CanonicalGradient

/-!
Article: main_krylov, thm:RFCS, actual positive-root metric coordinates.
Use: Construct the genuine canonical coordinate equivalence from the existing
positive matrix square root and its proved inverse, with actual symmetry
and exact normalization of the true minimizer Hessian.
Source: the already proved metricRoot inverse/square identities and mathlib
ContinuousLinearEquiv.equivOfInverse. No coordinate equivalence is assumed.
-/

namespace krylov.Nonlinear
noncomputable section
open Matrix krylov.Reference krylov.Secant
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The genuine continuous linear canonical coordinate equivalence constructed from the actual positive metric root.
Use: Normalize actual nonlinear errors without changing the original physical algorithm.
Article: main_krylov, thm:RFCS, genuine canonical metric normalization.
-/
def metricCoordinates (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) :
    EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ContinuousLinearEquiv.equivOfInverse (cgOperator (metricRoot base)) (cgOperator (metricRoot base)⁻¹)
    (fun v => by
      simp only [cgOperator,← mul_apply_eq_comp,← map_mul,nonsing_inv_mul _ (metricRoot_det_unit base hb),
        map_one,one_apply_eq_self])
    (fun v => by
      simp only [cgOperator,← mul_apply_eq_comp,← map_mul,mul_nonsing_inv _ (metricRoot_det_unit base hb),
        map_one,one_apply_eq_self])

/-- The actual canonical coordinate equivalence acts by the genuine positive metric root.
Use: Identify the true canonical primal norm.
Article: main_krylov, thm:RFCS, genuine canonical metric normalization.
Proof: Read the explicitly constructed forward continuous linear map.
-/
theorem metricCoordinates_apply (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (v : EuclideanSpace ℝ (Fin n)) : metricCoordinates base hb v=cgOperator (metricRoot base) v := rfl

/-- The actual inverse canonical coordinate equivalence acts by the genuine inverse positive metric root.
Use: Identify the true canonical gradient and Hessian congruence.
Article: main_krylov, thm:RFCS, genuine canonical metric normalization.
Proof: Read the explicitly constructed inverse continuous linear map.
-/
theorem metricCoordinates_symm_apply (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (v : EuclideanSpace ℝ (Fin n)) : (metricCoordinates base hb).symm v=cgOperator (metricRoot base)⁻¹ v := rfl

/-- The actual inverse metric coordinate map is self-adjoint.
Use: Discharge the genuine symmetry hypothesis of exact mixed self-concordance transport.
Article: main_krylov, thm:RFCS, genuine canonical metric normalization.
Proof: The existing positive metric root is symmetric; its true nonsingular matrix inverse is symmetric as well.
-/
theorem metricCoordinates_inverse_symmetric (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) :
    (metricCoordinates base hb).symm.toContinuousLinearMap.toLinearMap.IsSymmetric := by
  apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
  exact Matrix.isHermitian_iff_isSymm.mpr (metricRoot_isSymm base).inv

/-- The genuine minimizer Hessian is exactly the identity after the constructed actual positive-root coordinate congruence.
Use: Apply the actual self-concordant local Hessian estimate in the original prescribed canonical metric.
Article: main_krylov, thm:RFCS, genuine canonical metric normalization.
Proof: Evaluate the true coordinate derivative and reuse the proved exact inverse-root reconstruction of the base matrix.
-/
theorem coordinateDerivative_metric_zero (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (h₀ : H 0=cgOperator base) :
    coordinateDerivative (metricCoordinates base hb) H 0=ContinuousLinearMap.id ℝ _ := by
  apply ContinuousLinearMap.ext
  intro v
  change cgOperator (metricRoot base)⁻¹ (H ((metricCoordinates base hb).symm 0)
    (cgOperator (metricRoot base)⁻¹ v))=v
  rw [map_zero,h₀]
  simp only [cgOperator,← mul_apply_eq_comp,← map_mul,← Matrix.mul_assoc]
  change Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (relativeOperator base base) v=v
  rw [relativeOperator_base base hb,map_one,one_apply_eq_self]

end
end krylov.Nonlinear
