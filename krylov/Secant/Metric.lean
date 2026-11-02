import krylov.Secant.WindowBound
import chebyshev1.Spectral.OperatorNorm
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
Article: main_krylov, def:model, def:latest and apA:lem:flagcd.
Use: actual positive square roots fix canonical coordinates and the spectral
norm convention shared with the earlier articles; no unspecified whitening
matrix or entrywise matrix norm enters the definition of a perturbation budget.
Source: mathlib continuous functional calculus for positive definite matrices.
-/

namespace krylov.Secant
noncomputable section
open Matrix
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator
variable {n p : ℕ}

/-- The actual positive semidefinite square root used for canonical coordinates.
Use: the positive-definite premise in the lemmas makes this root invertible.
Article: main_krylov, def:model(c), A^(1/2).
Source: mathlib CFC.sqrt, positive continuous functional calculus. -/
def metricRoot (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt A

/-- The canonical relative form of a physical curvature perturbation.
Use: all canonical increments and output-segment budgets use the same base metric.
Article: main_krylov, def:model(c), A^(−1/2) E A^(−1/2). -/
def relativeOperator (A E : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (metricRoot A)⁻¹ * E * (metricRoot A)⁻¹

/-- The genuine spectral budget of a relative perturbation.
Use: reuse the earlier article's explicit Euclidean operator norm, independent
of a caller's active matrix-norm scope.
Article: main_krylov, def:model(c), the canonical spectral budgets. -/
def relativeBudget (A E : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  chebyshev1.opNorm (relativeOperator A E)

/-- Canonical congruence preserves real scalar multiples exactly.
Use: signed physical rank-one scenarios have their precise canonical budget scale.
Article: main_krylov, def:model(c) and thm:window.
Proof: multiplication by the fixed inverse roots is linear on either side. -/
theorem relativeOperator_smul (A E : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    relativeOperator A (c • E) = c • relativeOperator A E := by
  simp only [relativeOperator, Matrix.mul_smul, Matrix.smul_mul]

/-- Opposite physical perturbations have opposite actual canonical forms.
Use: the two indistinguishable hidden scenarios remain opposite after normalization.
Article: main_krylov, thm:window.
Proof: both fixed matrix multiplications preserve negation. -/
theorem relativeOperator_neg (A E : Matrix (Fin n) (Fin n) ℝ) :
    relativeOperator A (-E) = -relativeOperator A E := by
  simp only [relativeOperator, Matrix.mul_neg, Matrix.neg_mul]

/-- The actual canonical congruence preserves symmetry of a physical form.
Use: spectral norm bounds can be tested by the two shifted positive forms.
Article: main_krylov, def:model(c).
Proof: transpose the product and use symmetry of the inverse positive root. -/
theorem relativeOperator_isSymm (A E : Matrix (Fin n) (Fin n) ℝ) (hE : E.IsSymm) :
    (relativeOperator A E).IsSymm := by
  simp only [relativeOperator, Matrix.IsSymm, transpose_mul, transpose_nonsing_inv,
    (CFC.sqrt_nonneg A).posSemidef.1.isSymm.eq, metricRoot, hE.eq, Matrix.mul_assoc]

/-- Canonical relative congruence preserves the Loewner order of physical forms.
Use: transform both exact physical envelope inequalities in the same metric.
Article: main_krylov, thm:window.
Proof: compress the positive difference by the actual symmetric inverse root. -/
theorem relativeOperator_mono (A : Matrix (Fin n) (Fin n) ℝ)
    {E F : Matrix (Fin n) (Fin n) ℝ} (h : E ≤ F) :
    relativeOperator A E ≤ relativeOperator A F := by
  have hs : ((metricRoot A)⁻¹).IsSymm := by
    simp only [metricRoot, Matrix.IsSymm, transpose_nonsing_inv,
      (CFC.sqrt_nonneg A).posSemidef.1.isSymm.eq]
  simpa only [relativeOperator, hs.eq] using congruence_mono h (metricRoot A)⁻¹

/-- The genuine metric root squares to the original positive definite operator.
Use: cancellation of canonical coordinates and reconstruction of physical increments.
Article: main_krylov, def:model(c).
Source: mathlib CFC.sqrt_mul_sqrt_self.
Proof: the positive-definite matrix is positive semidefinite in Loewner order. -/
theorem metricRoot_square (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    metricRoot A * metricRoot A = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg

/-- The actual metric root is symmetric, with its chosen positive branch.
Use: identify inverse transposes in the canonical congruence formulas.
Article: main_krylov, def:model(c).
Proof: the CFC square root is positive semidefinite, hence real symmetric. -/
theorem metricRoot_isSymm (A : Matrix (Fin n) (Fin n) ℝ) : (metricRoot A).IsSymm :=
  (CFC.sqrt_nonneg A).posSemidef.1.isSymm

/-- A positive definite base has an invertible actual metric root.
Use: justify every inverse in the canonical coordinate change.
Article: main_krylov, def:model(c).
Proof: the determinant square equals the nonzero determinant of the base. -/
theorem metricRoot_det_unit (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    IsUnit (metricRoot A).det := by
  have hd := congrArg Matrix.det (metricRoot_square A hA)
  rw [det_mul] at hd
  apply isUnit_iff_ne_zero.mpr
  intro hz
  rw [hz, zero_mul] at hd
  exact hA.det_pos.ne' hd.symm

/-- The canonical relative form of the base itself is exactly the identity.
Use: canonical perturbations are measured from I, without a residual scale factor.
Article: main_krylov, def:model(c).
Proof: substitute the actual square root and cancel its two nonsingular inverses. -/
theorem relativeOperator_base (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    relativeOperator A A = 1 := by
  unfold relativeOperator
  conv_lhs => arg 1; arg 2; rw [← metricRoot_square A hA]
  rw [← Matrix.mul_assoc, nonsing_inv_mul _ (metricRoot_det_unit A hA), one_mul,
    mul_nonsing_inv _ (metricRoot_det_unit A hA)]

/-- Applying the metric root twice reconstructs a relative physical perturbation.
Use: the exact recursion A_(l+1)=A_l+A^(1/2) Ê_l A^(1/2).
Article: main_krylov, def:model(c), s2:eq:firstorder.
Proof: cancel the inverse root on each side of the relative congruence. -/
theorem relativeOperator_reconstruct (A E : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    metricRoot A * relativeOperator A E * metricRoot A = E := by
  simp only [relativeOperator, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (metricRoot A) (metricRoot A)⁻¹,
    mul_nonsing_inv _ (metricRoot_det_unit A hA), one_mul,
    nonsing_inv_mul _ (metricRoot_det_unit A hA), mul_one]

/-- The inverse of the actual canonical model is the direct metric-root congruence.
Use: square physical corrections transform into the stated canonical normal equation.
Article: main_krylov, apA:galerkin(a), Ĵ⁻¹=A¹/²J⁻¹A¹/².
Proof: reverse the three matrix factors and cancel the actual invertible inverse roots. -/
theorem relativeOperator_inv (A J : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    (relativeOperator A J)⁻¹ = metricRoot A * J⁻¹ * metricRoot A := by
  simp only [relativeOperator, Matrix.mul_inv_rev,
    nonsing_inv_nonsing_inv _ (metricRoot_det_unit A hA), Matrix.mul_assoc]

/-- Canonical defects normalize each actual observed diagonal product.
Use: a data-only definition; positivity is proved before division is used in estimates.
Article: main_krylov, def:latest, δ_ij = D_ij / sqrt(M_ii M_jj). -/
def canonicalDefect (M : Matrix (Fin p) (Fin p) ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  fun i j => defect M i j / Real.sqrt (M i i * M j j)

end
end krylov.Secant
