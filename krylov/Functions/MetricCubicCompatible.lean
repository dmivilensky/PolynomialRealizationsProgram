import krylov.Functions.MetricCubicRFC
import krylov.Tensor.HarmonicReferenceBudgets

/-!
Article: main_krylov, thm:H, actual cubic/native tensor dictionary.
Use: identify the genuine physical cubic third derivative in the unchanged
native RFC formula with the actual canonical tensor slices at computed CG
midpoint differences and the true terminal half-step.
Source: actual inverse-root congruence, linearity and true CG root transport.
-/

namespace krylov.Functions
noncomputable section
open Matrix krylov.Reference krylov.Nonlinear krylov.Secant krylov.Tensor krylov.Variation
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual matrix of a genuine canonical cubic Riesz slice.
Article: main_krylov, thm:H. -/
def cubicSliceMatrix (T : SymmetricCubic (EuclideanSpace ℝ (Fin n)))
    (v : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm (canonicalVariation T v)

/-- The true slice matrix represents exactly the actual cubic third variation.
Article: main_krylov, thm:H. -/
theorem cubicSliceMatrix_operator (T : SymmetricCubic (EuclideanSpace ℝ (Fin n)))
    (v : EuclideanSpace ℝ (Fin n)) :
    cgOperator (cubicSliceMatrix T v) = canonicalVariation T v :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).apply_symm_apply _

/-- The native physical cubic compatible increments are the true canonical
tensor midpoint slices, with no tensor dictionary assumed.
Article: main_krylov, thm:H. -/
theorem rfcCompatibleIncrements_metricCubic
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (T : SymmetricCubic (EuclideanSpace ℝ (Fin n))) (u : EuclideanSpace ℝ (Fin n)) (l : ℕ) :
    rfcCompatibleIncrements base hb (metricCubicVariation (metricCoordinates base hb) T) u l =
      cubicSliceMatrix T (referenceMidpointDrift base (cgOperator base u) l) := by
  apply (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).injective
  change cgOperator (rfcCompatibleIncrements base hb (metricCubicVariation (metricCoordinates base hb) T) u l) =
    cgOperator (cubicSliceMatrix T (referenceMidpointDrift base (cgOperator base u) l))
  have hmat W : cgOperator (physicalCanonicalMatrix base hb W) =
      coordinateCongruence (metricCoordinates base hb) W := physicalCanonicalMatrix_operator base hb W
  rw [rfcCompatibleIncrements,hmat,cubicSliceMatrix_operator,
    coordinateCongruence_metricCubicVariation]
  congr 1
  simp only [map_smul,map_add]
  rfl

/-- The native physical cubic correction slice is precisely its true final
canonical half-step slice. Article: main_krylov, thm:H. -/
theorem rfcCompatibleCorrection_metricCubic
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (T : SymmetricCubic (EuclideanSpace ℝ (Fin n))) (u : EuclideanSpace ℝ (Fin n)) (l : ℕ) :
    rfcCompatibleCorrection base hb (metricCubicVariation (metricCoordinates base hb) T) u l =
      cubicSliceMatrix T ((1/2 : ℝ) • canonicalCGStep base (cgOperator base u) l) := by
  apply (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).injective
  change cgOperator (rfcCompatibleCorrection base hb (metricCubicVariation (metricCoordinates base hb) T) u l) =
    cgOperator (cubicSliceMatrix T ((1/2 : ℝ) • canonicalCGStep base (cgOperator base u) l))
  have hmat W : cgOperator (physicalCanonicalMatrix base hb W) =
      coordinateCongruence (metricCoordinates base hb) W := physicalCanonicalMatrix_operator base hb W
  rw [rfcCompatibleCorrection,hmat,cubicSliceMatrix_operator,
    coordinateCongruence_metricCubicVariation]
  congr 1
  simp only [map_smul]
  rfl

/-- The true cubic-slice matrix has exactly the actual variation operator norm.
Article: main_krylov, thm:H. -/
theorem cubicSliceMatrix_norm (T : SymmetricCubic (EuclideanSpace ℝ (Fin n)))
    (v : EuclideanSpace ℝ (Fin n)) : ‖cubicSliceMatrix T v‖ = ‖canonicalVariation T v‖ := by
  rw [Matrix.cstar_norm_def]
  change ‖cgOperator (cubicSliceMatrix T v)‖ = _
  rw [cubicSliceMatrix_operator]

end
end krylov.Functions
