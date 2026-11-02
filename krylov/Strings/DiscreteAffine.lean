import krylov.Strings.DiscreteInverseSpectral
import jacobi.Finite.AffinePolynomials
import jacobi.Finite.AffineSpectrum

/-!
Article: `main_krylov`, `apC:lem:stieltjes`, physical spectral normalization.
A genuine positive affine change of finite spectral nodes preserves the
original probabilities. Reuse actual inverse spectral uniqueness and the
proved Jacobi affine-polynomial formula to identify every canonical
orthogonal polynomial, and hence the full Christoffel diagonal, under
the same physical spectral change of variable.
-/

namespace krylov.Strings.DiscreteInverse
noncomputable section
open Matrix Polynomial chebyshev1 chebyshev2 jacobi.Finite
open scoped BigOperators
variable {N : ℕ} (M : DiscreteMeasure (N+1))

/-- Genuine positive affine image of the original finite probability data. -/
def affineMeasure (c d : ℝ) (hc : 0<c) : DiscreteMeasure (N+1) where
  node i := c*M.node i+d
  distinct := by
    intro i j h
    apply M.distinct
    exact mul_left_cancel₀ hc.ne' (add_right_cancel h)
  weight := M.weight
  positive := M.positive
  probability := M.probability

/-- Canonical Jacobi reconstruction commutes with the same actual positive
affine spectral change, including all prescribed boundary weights. -/
theorem affineMeasure_reconstructed (c d : ℝ) (hc : 0<c) :
    (affineMeasure M c d hc).reconstructed=affine M.reconstructed c d := by
  symm
  apply unique_of_spectral_weights (affine M.reconstructed c d)
    (affineMeasure M c d hc).reconstructed
    (affine_irreducible M.reconstructed_irreducible hc.ne' d)
    (affineBasis M.reconstructed M.reconstructedBasis hc.le d)
    (affineMeasure M c d hc).reconstructedBasis rfl
    (affineMeasure M c d hc).distinct
  intro k
  have h := M.reconstructed_weight (Nat.succ_pos N) k
  have h' := (affineMeasure M c d hc).reconstructed_weight (Nat.succ_pos N) k
  have hzero : (⟨0,Nat.succ_pos N⟩ : Fin (N+1))=0 := by apply Fin.ext; simp
  rw [hzero] at h h'
  rw [affineBasis_weight, h, h']
  rfl

/-- The actual affine-image canonical orthogonal polynomial is precisely
the original canonical polynomial in the inverse physical coordinate. -/
theorem affineMeasure_orthogonalPolynomial (c d : ℝ) (hc : 0<c) (i : Fin (N+1)) :
    (affineMeasure M c d hc).orthogonalPolynomial i=
      (M.orthogonalPolynomial i).comp (C c⁻¹*(X-C d)) := by
  rw [← normalizedLeading_eq_orthogonalPolynomial, affineMeasure_reconstructed,
    normalizedLeading_affine M.reconstructed hc d i.val (by omega),
    normalizedLeading_eq_orthogonalPolynomial]

/-- Every actual Christoffel diagonal is invariant under the corresponding
positive affine spectral map and evaluation-point map. -/
theorem christoffelKernel_affine (c d : ℝ) (hc : 0<c) (m : ℕ) (a : ℝ) :
    krylov.Reference.christoffelKernel (affineMeasure M c d hc) m (c*a+d)=
      krylov.Reference.christoffelKernel M m a := by
  rw [krylov.Reference.christoffelKernel, krylov.Reference.christoffelKernel]
  apply Finset.sum_congr rfl
  intro i _
  rw [affineMeasure_orthogonalPolynomial, eval_comp, eval_mul, eval_C, eval_sub, eval_X, eval_C]
  have h : c⁻¹*(c*a+d-d)=a := by field_simp; ring
  rw [h]

/-- The source's actual spectral normalization ζ=λ/μ−1. -/
def normalizedMeasure (μ : ℝ) (hμ : 0<μ) : DiscreteMeasure (N+1) :=
  affineMeasure M μ⁻¹ (-1) (inv_pos.mpr hμ)

/-- Exact normalized physical nodes; all original probabilities are retained. -/
theorem normalizedMeasure_node (μ : ℝ) (hμ : 0<μ) (i : Fin (N+1)) :
    (normalizedMeasure M μ hμ).node i=M.node i/μ-1 := by
  change μ⁻¹*M.node i+(-1)=_
  ring

/-- Moving physical reference zero to ζ=−1 preserves every actual input
Christoffel diagonal, with no assumption on the degree or target measure. -/
theorem christoffelKernel_normalized (μ : ℝ) (hμ : 0<μ) (m : ℕ) :
    krylov.Reference.christoffelKernel (normalizedMeasure M μ hμ) m (-1)=
      krylov.Reference.christoffelKernel M m 0 := by
  simpa only [normalizedMeasure, mul_zero, zero_add] using
    christoffelKernel_affine M μ⁻¹ (-1) (inv_pos.mpr hμ) m 0

end
end krylov.Strings.DiscreteInverse
