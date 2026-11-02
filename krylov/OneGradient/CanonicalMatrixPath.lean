import krylov.Variation.FCResponse
import krylov.Stability.MetricRootRegularity
set_option autoImplicit false
/-!
Article: main_krylov, thm:I, original canonical increment path as actual matrices.
Use: specialize actual physical launch and XRFC expansion theorems to the
same canonical source scenario already used throughout the earlier stages.
Source: the genuine Euclidean star-algebra equivalence and the existing actual
canonicalFCPath calculus, with true positive metric-root cancellation.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.Secant krylov.Stability krylov.Variation
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The original canonical increment source as actual physical segment matrices.
Use: the fixed existing source operator sequence is recovered exactly below.
Article: main_krylov, thm:I, A_k=A+t A^(1/2)(sum_(l<k) E_l) A^(1/2). -/
def canonicalMatrixPath (base : Matrix (Fin n) (Fin n) ℝ)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (k : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm (canonicalFCPath base E t k)

/-- The actual physical matrix path has exactly the original canonical source operators.
Use: no new scenario, observation sequence or perturbation convention is introduced.
Article: main_krylov, thm:I.
Proof: the genuine Euclidean star-algebra equivalence cancels its actual inverse. -/
theorem canonical_matrix_path_operator (base : Matrix (Fin n) (Fin n) ℝ)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (k : ℕ) :
    cgOperator (canonicalMatrixPath base E t k)=canonicalFCPath base E t k :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).apply_symm_apply _

/-- The original physical canonical source is C2 from its true affine operator construction.
Use: primitive source regularity in the actual varying-prefix XRFC expansion is discharged.
Article: main_krylov, thm:I.
Proof: compose the existing actual analytic canonical path with the true
continuous linear inverse Euclidean matrix equivalence. -/
theorem canonical_matrix_path_contDiff (base : Matrix (Fin n) (Fin n) ℝ)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    ContDiffAt ℝ 2 (fun t => canonicalMatrixPath base E t k) 0 := by
  let L := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm.toAlgEquiv.toLinearMap.toContinuousLinearMap
  exact L.contDiff.contDiffAt.comp 0 (canonicalFCPath_calculus base E k).1.contDiffAt

/-- Zero canonical source size recovers each original actual reference matrix.
Use: actual reference full atom counts, trial histories and inverse domains are shared.
Article: main_krylov, thm:I.
Proof: the true canonical source operator is the original base at zero;
the genuine physical matrix/operator equivalence is injective. -/
theorem canonical_matrix_path_zero (base : Matrix (Fin n) (Fin n) ℝ)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : canonicalMatrixPath base E 0 k=base := by
  apply (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).injective
  change cgOperator (canonicalMatrixPath base E 0 k)=cgOperator base
  rw [canonical_matrix_path_operator]
  exact congrFun (canonicalFCPath_zero base E) k

/-- Symmetric original canonical increments give actual symmetric physical segment matrices.
Use: the source specialization retains the original admitted physical matrix scenario class.
Article: main_krylov, thm:I.
Proof: reuse the original true symmetric canonical operator path and the
actual real physical symmetry/operator correspondence. -/
theorem canonical_matrix_path_symmetric (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ l,(E l).IsSymm) (t : ℝ) (k : ℕ) :
    (canonicalMatrixPath base E t k).IsSymm := by
  apply Matrix.isHermitian_iff_isSymm.mp
  apply Matrix.isSymmetric_toEuclideanLin_iff.mp
  change (cgOperator (canonicalMatrixPath base E t k)).toLinearMap.IsSymmetric
  rw [canonical_matrix_path_operator]
  exact canonicalFCPath_symmetric base hb E hE t k

/-- The true normalized derivative increment of the physical source is
exactly its original supplied canonical matrix increment.
Use: the printed XRFC response uses the original E_l, with no surrogate derivative convention.
Article: main_krylov, thm:I.
Proof: the existing affine path gives its genuine cumulative physical derivative;
subtract consecutive real prefixes and cancel both actual positive metric roots. -/
theorem canonical_matrix_path_normalized_increment (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (l : ℕ) :
    let R := cgOperator (metricRoot base)⁻¹
    R*(deriv (fun t => cgOperator (canonicalMatrixPath base E t (l+1))) 0-
      deriv (fun t => cgOperator (canonicalMatrixPath base E t l)) 0)*R=cgOperator (E l) := by
  have hd (k : ℕ) : deriv (fun t => cgOperator (canonicalMatrixPath base E t k)) 0=cumulativeDrift base E k := by
    simp only [canonical_matrix_path_operator]
    exact (canonicalFCPath_calculus base E k).2.deriv
  dsimp only
  rw [hd,hd]
  have he : cumulativeDrift base E (l+1)-cumulativeDrift base E l=cgOperator (metricRoot base*E l*metricRoot base) := by
    simp only [cumulativeDrift,Finset.sum_range_succ,Matrix.mul_add,Matrix.add_mul,map_add,add_sub_cancel_left,cgOperator]
  rw [he]
  simp only [cgOperator,← map_mul]
  congr 1
  calc
    _ = ((metricRoot base)⁻¹*metricRoot base)*E l*(metricRoot base*(metricRoot base)⁻¹) := by noncomm_ring
    _ = E l := by rw [Matrix.nonsing_inv_mul _ (metricRoot_det_unit base hb),
      Matrix.mul_nonsing_inv _ (metricRoot_det_unit base hb),Matrix.one_mul,Matrix.mul_one]

end
end krylov.OneGradient
