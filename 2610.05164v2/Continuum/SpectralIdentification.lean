import «2610.05164v2».Continuum.GramEigenvalues
import «2610.05164v2».Continuum.AtomicOperator

/-!
Article: 2610.05164v2, Theorem 2.3.
The article's two continuum operators have equal sorted spectra, with the same zero-padding
convention even when their kernels differ.
Use: `«2610.05164v2».Continuum.density_kernel_eigenvalue_eq` feeds
`«2610.05164v2».Continuum.kernelEigenvalue_square_integral` (The quadratic spectral observation is
the literal double integral printed in Section 2.2, for every nonnegative integrable density).
Proof chain: `«2610.05164v2».Packing.packed_spectral_distance` — 2610.05164v2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory. The needed
form is proved here.
-/
namespace «2610.05164v2».Continuum
noncomputable section
open MeasureTheory

/--
Defines `densitySpectralData` of type `PositiveSpectralData (densityOperator m)` by
`positiveSpectralData _ (densityOperator_isCompact hm) (densityOperator_positive hm hn)
(densityOperator_isTraceClass hm)`.

Use: `«2610.05164v2».Continuum.kernelEigenvalue_square_integral` uses this definition to
establish exact identity `(∑' j, kernelEigenvalue hm hn j^2) = ∫ x, ∫ y, m x*m y*exp
(-2*|x-y|)`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.
-/
def densitySpectralData {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) :
    PositiveSpectralData (densityOperator m) :=
  positiveSpectralData _ (densityOperator_isCompact hm) (densityOperator_positive hm hn)
    (densityOperator_isTraceClass hm)

/--
The article's two continuum operators have equal sorted spectra, with the same zero-padding
convention even when their kernels differ.

Exact identity `D.eigenvalue = kernelEigenvalue hm hn`.

Use: `«2610.05164v2».Continuum.kernelEigenvalue_square_integral` rewrites with this identity to
establish exact identity `(∑' j, kernelEigenvalue hm hn j^2) = ∫ x, ∫ y, m x*m y*exp
(-2*|x-y|)`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.gram_eigenvalue_eq`,
`«2610.05164v2».Continuum.evaluationOperator_adjoint_comp` with the arguments shown in the
proof.
-/
theorem density_kernel_eigenvalue_eq {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
    (D : PositiveSpectralData (densityOperator m)) : D.eigenvalue = kernelEigenvalue hm hn := by
  have h := gram_eigenvalue_eq (evaluationOperator hm hn)
  rw [evaluationOperator_adjoint_comp] at h
  exact h D (kernelSpectralData hm hn)

end
end «2610.05164v2».Continuum
