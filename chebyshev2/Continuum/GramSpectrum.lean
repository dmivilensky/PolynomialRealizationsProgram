import chebyshev2.Continuum.KernelOperator
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
Article: chebyshev2, Theorem 3.1.
Equality of nonzero eigenvalue multiplicities for the continuum density.
Use: `chebyshev2.Continuum.densityKernelEigenspaceEquiv` feeds
`chebyshev2.GroundState.kernel_ground_simple` (The literal leading eigenspace of the article's
L2 kernel has dimension one).
Proof chain: `chebyshev2.GroundState.kernel_ground_simple` — chebyshev2, Theorem 3.1; Sharp
ground-state variational principle, ODE, simplicity and intrinsic coordinate.
Source: Riesz and Sz.-Nagy, Functional Analysis — nonzero spectra of Gram operators. The needed form
is proved here.
-/
namespace chebyshev2.Continuum
noncomputable section
open Module Module.End
set_option backward.isDefEq.respectTransparency false

variable {E F : Type*} [AddCommGroup E] [AddCommGroup F] [Module ℝ E] [Module ℝ F]

/--
AB and BA have linearly equivalent eigenspaces at every nonzero eigenvalue. This equivalence
preserves multiplicities without choosing eigenvectors.

Use: `chebyshev2.Continuum.densityKernelEigenspaceEquiv` uses this definition in the
displayed construction of `densityKernelEigenspaceEquiv`. Its inputs and component formulas are
fixed by that definition.

Article: chebyshev2, Theorem 3.1 via `chebyshev2.GroundState.kernel_ground_simple`.

Source: Riesz and Sz.-Nagy, Functional Analysis — nonzero spectra of Gram operators.
-/
def gramEigenspaceEquiv (A : E →ₗ[ℝ] F) (B : F →ₗ[ℝ] E) {μ : ℝ} (hμ : μ ≠ 0) :
    eigenspace (B.comp A) μ ≃ₗ[ℝ] eigenspace (A.comp B) μ where
  toFun u := ⟨A u, by
    rw [mem_eigenspace_iff]
    change A (B (A u)) = μ • A u
    have hu : B (A u) = μ • (u : E) := mem_eigenspace_iff.mp u.property
    rw [hu, map_smul]⟩
  invFun v := ⟨μ⁻¹ • B v, by
    rw [mem_eigenspace_iff]
    change B (A (μ⁻¹ • B v)) = μ • (μ⁻¹ • B v)
    have hv : A (B v) = μ • (v : F) := mem_eigenspace_iff.mp v.property
    simp only [map_smul, hv, smul_smul, inv_mul_cancel₀ hμ, mul_inv_cancel₀ hμ, one_smul]⟩
  left_inv u := by
    apply Subtype.ext
    change μ⁻¹ • B (A u) = (u : E)
    have hu : B (A u) = μ • (u : E) := mem_eigenspace_iff.mp u.property
    rw [hu, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  right_inv v := by
    apply Subtype.ext
    change A (μ⁻¹ • B v) = (v : F)
    have hv : A (B v) = μ • (v : F) := mem_eigenspace_iff.mp v.property
    rw [map_smul, hv, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  map_add' u v := by
    apply Subtype.ext
    exact A.map_add _ _
  map_smul' c u := by
    apply Subtype.ext
    exact A.map_smul c u

/--
Exact identity `Module.finrank ℝ (eigenspace (B.comp A) μ) = Module.finrank ℝ (eigenspace
(A.comp B) μ)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 3.1.

Source: Riesz and Sz.-Nagy, Functional Analysis — nonzero spectra of Gram operators.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem gramEigenspace_finrank (A : E →ₗ[ℝ] F) (B : F →ₗ[ℝ] E) {μ : ℝ} (hμ : μ ≠ 0) :
    Module.finrank ℝ (eigenspace (B.comp A) μ) = Module.finrank ℝ (eigenspace (A.comp B) μ) :=
  (gramEigenspaceEquiv A B hμ).finrank_eq

/--
Equality of nonzero eigenvalue multiplicities for the continuum density.

Use: `chebyshev2.GroundState.kernel_ground_simple` rewrites with this definition to
establish exact identity `Module.finrank ℝ (eigenspace (kernelOperator hm hn).toLinearMap
(kernelEigenvalue hm hn 0))=1`.

Article: chebyshev2, Theorem 3.1 via `chebyshev2.GroundState.kernel_ground_simple`.

Source: Riesz and Sz.-Nagy, Functional Analysis — nonzero spectra of Gram operators.

Proof: Use the identities/estimates `chebyshev2.Continuum.evaluationOperator_adjoint_comp`
with the arguments shown in the proof.
-/
def densityKernelEigenspaceEquiv {m : ℝ → ℝ} (hm : MeasureTheory.Integrable m) (hn : ∀ x, 0 ≤ m x)
    {μ : ℝ} (hμ : μ ≠ 0) :
    eigenspace (densityOperator m).toLinearMap μ ≃ₗ[ℝ]
      eigenspace (kernelOperator hm hn).toLinearMap μ := by
  -- Use the identities/estimates `chebyshev2.Continuum.evaluationOperator_adjoint_comp`
  -- with the arguments shown in the proof.
  have he := evaluationOperator_adjoint_comp hm hn
  have he' : (densityOperator m).toLinearMap =
      ((evaluationOperator hm hn).adjoint.toLinearMap).comp (evaluationOperator hm hn).toLinearMap :=
    congrArg ContinuousLinearMap.toLinearMap he.symm
  rw [he']
  exact gramEigenspaceEquiv _ _ hμ

end
end chebyshev2.Continuum
