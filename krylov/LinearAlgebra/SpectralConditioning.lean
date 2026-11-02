import krylov.LinearAlgebra.Pseudoinverse
import krylov.LinearAlgebra.NormOrder
import chebyshev1.Spectral.OperatorNorm
import Mathlib.Analysis.Matrix.PosDef

/-!
Article: main_krylov, lem:projected-residual, conditioning of normalized models.
Use: discharge inverse and Gram bounds from the stated genuine eigenvalue
interval, including an empty coefficient space.
Source: the existing spectral pseudoinverse, the earlier spectral norm formula,
and mathlib's finite real spectral theorem.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix chebyshev1
open scoped Matrix.Norms.L2Operator
variable {p : ℕ}

/-- A Hermitian matrix with all eigenvalues in a nonnegative interval has the corresponding spectral upper bound.
Use: the source Gram spectral interval supplies the actual rectangular synthesis bound.
Article: main_krylov, lem:projected-residual, ‖TᵀT‖≤b.
Proof: specialize the existing polynomial spectral norm identity to the identity polynomial. -/
theorem spectral_norm_le_of_eigenvalues (H : Matrix (Fin p) (Fin p) ℝ) (hH : H.IsHermitian)
    {b : ℝ} (hb : 0≤b) (he : ∀ i, 0≤hH.eigenvalues i ∧ hH.eigenvalues i≤b) : ‖H‖≤b := by
  have hn := opNorm_aeval_eq (Polynomial.X : Polynomial ℝ) H hH
  simp only [Polynomial.aeval_X, Polynomial.eval_X, opNorm] at hn
  rw [hn, pi_norm_le_iff_of_nonneg hb]
  intro i
  rw [Real.norm_of_nonneg (he i).1]
  exact (he i).2

/-- The true nonsingular inverse spectral norm is the supremum norm of reciprocal eigenvalues.
Use: pass from the positive lower spectral endpoint to a length-independent correction constant.
Article: main_krylov, lem:projected-residual, normalized inverse bound.
Proof: identify the genuine inverse with the previously constructed spectral
pseudoinverse and remove its two unitary factors by norm invariance. -/
theorem inverse_norm_eq_eigenvalues (H : Matrix (Fin p) (Fin p) ℝ) (hH : H.IsHermitian)
    (hu : IsUnit H.det) : ‖H⁻¹‖=‖fun i => (hH.eigenvalues i)⁻¹‖ := by
  -- The reused spectral inverse is the actual matrix inverse on this proved domain.
  rw [← pseudoinverse_eq_inv H hH hu]
  change ‖(hH.eigenvectorUnitary : Matrix (Fin p) (Fin p) ℝ)*
    diagonal (fun i => (hH.eigenvalues i)⁻¹)*(hH.eigenvectorUnitary : Matrix (Fin p) (Fin p) ℝ)ᵀ‖=_
  rw [← conjTranspose_eq_transpose_of_trivial, ← Matrix.star_eq_conjTranspose,
    ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
    Matrix.l2_opNorm_diagonal]

/-- A positive lower endpoint of the actual model spectrum proves both nonsingularity and the inverse bound.
Use: no inverse-domain or inverse-size premise remains assumed in the RFC residual estimate.
Article: main_krylov, lem:projected-residual, ‖Ĥ⁻¹‖≤1/a.
Proof: positive eigenvalues imply genuine positive definiteness; invert their
lower bound in the proved exact spectral inverse-norm formula. -/
theorem inverse_bound_of_eigenvalues (H : Matrix (Fin p) (Fin p) ℝ) (hH : H.IsHermitian)
    {a : ℝ} (ha : 0<a) (he : ∀ i, a≤hH.eigenvalues i) :
    IsUnit H.det ∧ ‖H⁻¹‖≤a⁻¹ := by
  have hp : H.PosDef := hH.posDef_iff_eigenvalues_pos.mpr fun i => ha.trans_le (he i)
  have hu : IsUnit H.det := Matrix.isUnit_iff_isUnit_det H |>.mp hp.isUnit
  refine ⟨hu, ?_⟩
  rw [inverse_norm_eq_eigenvalues H hH hu, pi_norm_le_iff_of_nonneg (inv_nonneg.mpr ha.le)]
  intro i
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (ha.trans_le (he i)).le)]
  exact inv_anti₀ ha (he i)

/-- A true lower spectral endpoint bounds the actual Euclidean quadratic form.
Use: the normalized Gram lower bound controls coefficients of the new recorded unit step.
Article: main_krylov, lem:projected-residual, TᵀT⪰aI.
Proof: diagonalize the shifted form in the reused spectral coordinates; its
nonnegative diagonal makes it positive semidefinite, then test its actual vector form. -/
theorem spectral_lower_form (H : Matrix (Fin p) (Fin p) ℝ) (hH : H.IsHermitian)
    {a : ℝ} (he : ∀ i, a≤hH.eigenvalues i) (v : EuclideanSpace ℝ (Fin p)) :
    a*‖v‖^2 ≤ inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) H v) := by
  -- Shift the genuine spectral form before testing the physical coefficient vector.
  let B := SpectralBasis.ofHermitian H hH
  have hp : ((-a) • (1 : Matrix (Fin p) (Fin p) ℝ)+H).PosSemidef := by
    rw [← coordinates_posSemidef_iff B, coordinates_lower_shift, posSemidef_diagonal_iff]
    intro i
    change 0≤-a+hH.eigenvalues i
    linarith [he i]
  have ht := hp.dotProduct_mulVec_nonneg (WithLp.ofLp v)
  simp only [star_trivial] at ht
  rw [← Matrix.inner_toEuclideanCLM] at ht
  simp only [map_add, map_smul, map_one, _root_.add_apply,
    _root_.smul_apply, one_apply_eq_self] at ht
  change 0 ≤ inner ℝ v ((-a) • v+Matrix.toEuclideanCLM (𝕜 := ℝ) H v) at ht
  rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq] at ht
  linarith

end
end krylov.LinearAlgebra
