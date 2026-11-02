import krylov.Reference.CG
import krylov.Secant.Metric
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
Article: main_krylov, s2:eq:cg and lem:terminal-fibre, actual reference step coordinates.
Use: all reference steps and normalized canonical directions are computed by
the concrete CG run and the actual positive metric root.
Source: the proved concrete recurrence, actual metric root and zero-safe norm normalization.
-/

namespace krylov.Reference
noncomputable section
open Matrix krylov.Secant
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
variable {n : ℕ}

/-- Actual quadratic reference operator in its genuine Euclidean space.
Use: the same operator supplies the actual CG recurrence and the static comparison history.
Article: main_krylov, s2:eq:cg, reference Hessian A. -/
def cgOperator (base : Matrix (Fin n) (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) base

/-- Actual line length in the concrete quadratic CG run.
Use: defines the actual reference step independently of any terminal data-fibre result.
Article: main_krylov, s2:eq:cg, α_k. -/
def cgLine (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) : ℝ :=
  let r := cgRun (cgOperator base) g k
  lineLength r.gradient r.direction (cgOperator base r.direction)

/-- Actual physical step of the concrete quadratic CG run.
Use: its canonical norm is the actual square root of the reference energy drop.
Article: main_krylov, s2:eq:cg, s_k⁰=α_kd_k⁰. -/
def cgStep (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    EuclideanSpace ℝ (Fin n) := cgLine base g k • (cgRun (cgOperator base) g k).direction

/-- Actual canonical step computed from the genuine physical CG step and genuine positive metric root.
Use: fixes the reference geometry used by every planar data-fibre construction.
Article: main_krylov, s2:eq:cg, A^(1/2)s_k⁰. -/
def canonicalCGStep (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    EuclideanSpace ℝ (Fin n) := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base) (cgStep base g k)

/-- Actual normalized canonical step of the concrete CG run, zero after a zero step.
Use: source orthonormal reference directions are tied to the actual executed recurrence.
Article: main_krylov, s2:eq:cg, ŝ_k. -/
def canonicalCGUnitStep (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    EuclideanSpace ℝ (Fin n) := NormedSpace.normalize (canonicalCGStep base g k)

/-- A positive physical reference matrix has its actual symmetric positive quadratic operator.
Use: discharges the operator hypotheses of global CG consistency with the true reference base.
Article: main_krylov, lem:terminal-fibre, positive quadratic reference.
Proof: the true matrix/operator correspondence preserves symmetry, and the
actual Euclidean inner product is exactly the positive physical quadratic form. -/
theorem cgOperator_positive (base : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef) :
    (cgOperator base).toLinearMap.IsSymmetric ∧
      ∀ v : EuclideanSpace ℝ (Fin n), v≠0 → 0 < inner ℝ v (cgOperator base v) := by
  -- Preserve the actual Euclidean vector when transferring the positive physical quadratic form.
  constructor
  · exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hbase.1
  · intro v hv
    have ho : WithLp.ofLp v≠0 := by
      intro hz
      apply hv
      ext i
      exact congrArg (fun a : Fin n → ℝ => a i) hz
    simpa only [cgOperator, Matrix.inner_toEuclideanCLM, star_trivial] using
      hbase.dotProduct_mulVec_pos ho

/-- A nonzero actual canonical CG step has a nonzero actual line length.
Use: inverse rescaling of the true reference direction is justified before division.
Article: main_krylov, lem:terminal-fibre, nondegenerate reference step.
Proof: a zero line length would make its true physical step and true canonical image zero. -/
theorem cgLine_ne_zero (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hs : canonicalCGStep base g k≠0) : cgLine base g k≠0 := by
  intro hz
  apply hs
  simp only [canonicalCGStep, cgStep, hz, zero_smul, map_zero]

/-- The actual canonical CG direction is the actual canonical step divided by its true line length.
Use: reference step orthogonality is applied to the genuine oracle query directions.
Article: main_krylov, lem:terminal-fibre, normalized direction conversion.
Proof: expand the actual step, move its scalar through the actual root action and cancel its nonzero line length. -/
theorem canonicalCG_direction (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hs : canonicalCGStep base g k≠0) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base) (cgRun (cgOperator base) g k).direction=
      (cgLine base g k)⁻¹ • canonicalCGStep base g k := by
  rw [canonicalCGStep, cgStep, map_smul, smul_smul, inv_mul_cancel₀ (cgLine_ne_zero base g k hs), one_smul]

end
end krylov.Reference
