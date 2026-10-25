import chebyshev2.Continuum.AtomicOperator
import chebyshev2.Continuum.FiniteTrace
import chebyshev2.Continuum.GramEigenvalues
import Mathlib.Analysis.Matrix.Spectrum

/-!
Article: chebyshev2, Theorem 2.3.
Equality of sorted atomic and matrix spectra, including zero padding.
Use: `chebyshev2.Continuum.atomic_matrix_eigenvalue_eq` feeds
`chebyshev2.Packing.packed_spectral_distance` (Theorem 2.3, equation (7), for the full fiber
including zero edges).
Proof chain: `chebyshev2.Packing.packed_spectral_distance` — chebyshev2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
-/
namespace chebyshev2.Continuum
noncomputable section
open Real
open scoped InnerProductSpace BigOperators Classical
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/--
The actual matrix operator equals the finite synthesis Gram operator.

Exact identity `Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) (atomicMatrix w y) = (familySynthesis
(weightedFeature w y)).adjoint ∘L familySynthesis (weightedFeature w y)`.

Use: `chebyshev2.Continuum.atomic_matrix_eigenvalue_eq` rewrites with this identity to
establish exact identity `(atomicSpectralData w y hw).eigenvalue = (atomicMatrixSpectralData w
y).eigenvalue`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Use the identities/estimates `chebyshev2.Continuum.atomicOperator_matrix` with the
arguments shown in the proof.
-/
theorem atomicMatrix_operator (w y : ι → ℝ) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) (atomicMatrix w y) =
      (familySynthesis (weightedFeature w y)).adjoint ∘L familySynthesis (weightedFeature w y) := by
  -- Use the identities/estimates `chebyshev2.Continuum.atomicOperator_matrix` with the
  -- arguments shown in the proof.
  apply ContinuousLinearMap.coe_injective
  change Matrix.toEuclideanLin (atomicMatrix w y) = _
  rw [← atomicOperator_matrix w y]
  exact (LinearMap.toMatrix (EuclideanSpace.basisFun ι ℝ).toBasis
    (EuclideanSpace.basisFun ι ℝ).toBasis).symm_apply_apply _

omit [DecidableEq ι] in
/--
Compactness of the displayed operator: `IsCompactOperator (atomicOperator w y)`.

Use: `chebyshev2.Continuum.atomicSpectralData` uses this assertion in the displayed
construction of `atomicSpectralData`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Use the identities/estimates `chebyshev2.Continuum.atomicOperator_gram` with the
arguments shown in the proof.
-/
theorem atomicOperator_isCompact (w y : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    IsCompactOperator (atomicOperator w y) := by
  rw [← atomicOperator_gram w y hw]
  exact (isCompactOperator_of_locallyCompactSpace_rng (familySynthesis (weightedFeature w y))).comp_clm _

omit [DecidableEq ι] in
/--
The precise assertion is `(atomicOperator w y).IsPositive`.

Use: `chebyshev2.Continuum.atomicSpectralData` uses this assertion in the displayed
construction of `atomicSpectralData`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Use the identities/estimates `chebyshev2.Continuum.atomicOperator_gram` with the
arguments shown in the proof.
-/
theorem atomicOperator_positive (w y : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (atomicOperator w y).IsPositive := by
  rw [← atomicOperator_gram w y hw]
  exact ContinuousLinearMap.isPositive_self_comp_adjoint _

omit [DecidableEq ι] in
/--
The precise assertion is `TraceBound (atomicOperator w y) (∑ i, w i)`.

Use: `chebyshev2.Continuum.atomicSpectralData` uses this assertion in the displayed
construction of `atomicSpectralData`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Use the identities/estimates `chebyshev2.Continuum.traceBound_tsum`,
`chebyshev2.Continuum.TraceBound.smul`,
`chebyshev2.Continuum.featureProjection_traceBound` with the arguments shown in the proof.
-/
theorem atomicOperator_traceBound (w y : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    TraceBound (atomicOperator w y) (∑ i, w i) := by
  have h := traceBound_tsum (f := fun i => w i • featureProjection (y i))
    (Summable.of_finite) (Summable.of_finite) (fun i => by
      simpa only [abs_of_nonneg (hw i),mul_one] using (featureProjection_traceBound (y i)).smul (w i))
  simpa only [tsum_fintype,atomicOperator] using h

/--
Defines `atomicSpectralData` of type `PositiveSpectralData (atomicOperator w y)` by
`positiveSpectralData _ (atomicOperator_isCompact w y hw) (atomicOperator_positive w y hw)
(atomicOperator_traceBound w y hw).isTraceClass`.

Use: `chebyshev2.Continuum.atomic_matrix_eigenvalue_eq` uses this definition to establish
exact identity `(atomicSpectralData w y hw).eigenvalue = (atomicMatrixSpectralData w
y).eigenvalue`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.
-/
def atomicSpectralData (w y : ι → ℝ) (hw : ∀ i, 0 ≤ w i) : PositiveSpectralData (atomicOperator w y) :=
  positiveSpectralData _ (atomicOperator_isCompact w y hw) (atomicOperator_positive w y hw)
    (atomicOperator_traceBound w y hw).isTraceClass

/--
Defines `atomicMatrixSpectralData` of type `PositiveSpectralData (Matrix.toEuclideanCLM (𝕜 :=
ℝ) (n := ι) (atomicMatrix w y))` by `positiveSpectralData _
(isCompactOperator_of_locallyCompactSpace_dom _) (by rw [atomicMatrix_operator]; exact
ContinuousLinearMap.isPositive_adjoint_comp_self _) (euclidean_isTraceClass _)`.

Use: `chebyshev2.Continuum.atomic_matrix_eigenvalue_eq` uses this definition to establish
exact identity `(atomicSpectralData w y hw).eigenvalue = (atomicMatrixSpectralData w
y).eigenvalue`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.
-/
def atomicMatrixSpectralData (w y : ι → ℝ) : PositiveSpectralData (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) (atomicMatrix w y)) :=
  positiveSpectralData _ (isCompactOperator_of_locallyCompactSpace_dom _) (by
    rw [atomicMatrix_operator]; exact ContinuousLinearMap.isPositive_adjoint_comp_self _)
    (euclidean_isTraceClass _)

/--
Equality of sorted atomic and matrix spectra, including zero padding.

Exact identity `(atomicSpectralData w y hw).eigenvalue = (atomicMatrixSpectralData w
y).eigenvalue`.

Use: `chebyshev2.Packing.Jacobi.density_atomic_spectral_distance` uses this identity to
establish the bound stated in that declaration.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Use the identities/estimates `chebyshev2.Continuum.gram_eigenvalue_eq`,
`chebyshev2.Continuum.atomicOperator_gram`,
`chebyshev2.Continuum.atomicMatrix_operator` with the arguments shown in the proof.
-/
theorem atomic_matrix_eigenvalue_eq (w y : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (atomicSpectralData w y hw).eigenvalue = (atomicMatrixSpectralData w y).eigenvalue := by
  have h := gram_eigenvalue_eq (familySynthesis (weightedFeature w y))
  rw [← atomicMatrix_operator,atomicOperator_gram w y hw] at h
  exact (h _ _).symm

end
end chebyshev2.Continuum
