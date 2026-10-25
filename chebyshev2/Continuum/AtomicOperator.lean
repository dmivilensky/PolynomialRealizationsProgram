import chebyshev2.Continuum.GramSpectrum
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Article: chebyshev2, Theorem 2.3.
Atomic and matrix eigenspaces agree at every nonzero eigenvalue.
Use: `chebyshev2.Continuum.atomicOperator_matrix` feeds
`chebyshev2.Continuum.atomicMatrix_operator` (The actual matrix operator equals the finite
synthesis Gram operator).
Proof chain: `chebyshev2.Packing.packed_spectral_distance` — chebyshev2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
-/
namespace chebyshev2.Continuum
noncomputable section
open MeasureTheory Real
open scoped InnerProductSpace BigOperators Classical
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι]

/--
Defines `familySynthesis` of type `EuclideanSpace ℝ ι →L[ℝ] FeatureSpace` by `∑ i,
InnerProductSpace.rankOne ℝ (v i) (EuclideanSpace.basisFun ι ℝ i)`.

Use: `chebyshev2.Continuum.atomicEigenspaceEquiv` uses this definition in the displayed
construction of `atomicEigenspaceEquiv`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.
-/
def familySynthesis (v : ι → FeatureSpace) : EuclideanSpace ℝ ι →L[ℝ] FeatureSpace :=
  ∑ i, InnerProductSpace.rankOne ℝ (v i) (EuclideanSpace.basisFun ι ℝ i)

/--
Exact identity `familySynthesis v (EuclideanSpace.basisFun ι ℝ i) = v i`.

Use: `chebyshev2.Continuum.familySynthesis_adjoint_coordinate` rewrites with this identity
to establish the identity `(EuclideanSpace.basisFun ι ℝ).repr ((familySynthesis v).adjoint u)
i = inner ℝ (v i) u`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Separate `j=i` from its negation; prove the goal under each of these mutually exclusive
hypotheses.
-/
theorem familySynthesis_basis (v : ι → FeatureSpace) (i : ι) :
    familySynthesis v (EuclideanSpace.basisFun ι ℝ i) = v i := by
  -- Separate `j=i` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  simp only [familySynthesis,sum_apply,InnerProductSpace.rankOne_apply]
  have he (j : ι) : inner ℝ (EuclideanSpace.basisFun ι ℝ j) (EuclideanSpace.basisFun ι ℝ i) • v j =
      if j=i then v i else 0 := by
    by_cases h : j=i
    · subst j
      simp
    · rw [(EuclideanSpace.basisFun ι ℝ).orthonormal.inner_eq_zero h]
      simp [h]
  simp only [he]
  simp

/--
Exact identity `(EuclideanSpace.basisFun ι ℝ).repr ((familySynthesis v).adjoint u) i = inner ℝ
(v i) u`.

Use: `chebyshev2.Continuum.familySynthesis_gram` rewrites with this identity to establish
exact identity `familySynthesis v ∘L (familySynthesis v).adjoint = ∑ i,
InnerProductSpace.rankOne ℝ (v i) (v i)`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Use the identities/estimates `chebyshev2.Continuum.familySynthesis_basis` with the
arguments shown in the proof.
-/
theorem familySynthesis_adjoint_coordinate (v : ι → FeatureSpace) (u : FeatureSpace) (i : ι) :
    (EuclideanSpace.basisFun ι ℝ).repr ((familySynthesis v).adjoint u) i = inner ℝ (v i) u := by
  rw [OrthonormalBasis.repr_apply_apply,ContinuousLinearMap.adjoint_inner_right,familySynthesis_basis]

/--
Exact identity `familySynthesis v ∘L (familySynthesis v).adjoint = ∑ i,
InnerProductSpace.rankOne ℝ (v i) (v i)`.

Use: `chebyshev2.Continuum.atomicOperator_gram` rewrites with this identity to establish
exact identity `familySynthesis (weightedFeature w y) ∘L (familySynthesis (weightedFeature w
y)).adjoint = atomicOperator w y`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Use the identities/estimates
`chebyshev2.Continuum.familySynthesis_adjoint_coordinate`,
`chebyshev2.Continuum.familySynthesis_basis` with the arguments shown in the proof.
-/
theorem familySynthesis_gram (v : ι → FeatureSpace) :
    familySynthesis v ∘L (familySynthesis v).adjoint = ∑ i, InnerProductSpace.rankOne ℝ (v i) (v i) := by
  apply ContinuousLinearMap.ext
  intro u
  change familySynthesis v ((familySynthesis v).adjoint u) = _
  rw [← (EuclideanSpace.basisFun ι ℝ).sum_repr ((familySynthesis v).adjoint u),map_sum]
  simp only [map_smul,familySynthesis_basis,familySynthesis_adjoint_coordinate,sum_apply,
    InnerProductSpace.rankOne_apply]

/--
The finite Gram matrix of the synthesis map, with actual Euclidean coordinates.

Exact identity `LinearMap.toMatrix (EuclideanSpace.basisFun ι ℝ).toBasis
(EuclideanSpace.basisFun ι ℝ).toBasis ((familySynthesis v).adjoint ∘L familySynthesis
v).toLinearMap = (fun i j => inner ℝ (v i) (v j))`.

Use: `chebyshev2.Continuum.atomicOperator_matrix` rewrites with this identity to establish
the identity stated in that declaration.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Use the identities/estimates
`chebyshev2.Continuum.familySynthesis_adjoint_coordinate`,
`chebyshev2.Continuum.familySynthesis_basis` with the arguments shown in the proof.
-/
theorem familySynthesis_matrix (v : ι → FeatureSpace) [DecidableEq ι] :
    LinearMap.toMatrix (EuclideanSpace.basisFun ι ℝ).toBasis (EuclideanSpace.basisFun ι ℝ).toBasis
      ((familySynthesis v).adjoint ∘L familySynthesis v).toLinearMap =
        (fun i j => inner ℝ (v i) (v j)) := by
  -- Use the identities/estimates
  -- `chebyshev2.Continuum.familySynthesis_adjoint_coordinate`,
  -- `chebyshev2.Continuum.familySynthesis_basis` with the arguments shown in the proof.
  ext i j
  rw [LinearMap.toMatrix_apply]
  change (EuclideanSpace.basisFun ι ℝ).repr ((familySynthesis v).adjoint (familySynthesis v
    (EuclideanSpace.basisFun ι ℝ j))) i = _
  rw [familySynthesis_adjoint_coordinate,familySynthesis_basis]

/--
Defines `weightedFeature` of type `FeatureSpace` by `sqrt (w i) • feature (y i)`.

Use: `chebyshev2.Continuum.atomicEigenspaceEquiv` uses this definition in the displayed
construction of `atomicEigenspaceEquiv`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.
-/
def weightedFeature (w y : ι → ℝ) (i : ι) : FeatureSpace := sqrt (w i) • feature (y i)

/--
Defines `atomicOperator` of type `FeatureSpace →L[ℝ] FeatureSpace` by `∑ i, w i •
featureProjection (y i)`.

Use: `chebyshev2.Continuum.atomicEigenspaceEquiv` uses this definition in the displayed
construction of `atomicEigenspaceEquiv`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.
-/
def atomicOperator (w y : ι → ℝ) : FeatureSpace →L[ℝ] FeatureSpace :=
  ∑ i, w i • featureProjection (y i)

/--
Defines `atomicMatrix` of type `Matrix ι ι ℝ` by `fun i j => sqrt (w i) * sqrt (w j) * exp (-|y
i-y j|)`.

Use: `chebyshev2.Continuum.atomicEigenspaceEquiv` uses this definition in the displayed
construction of `atomicEigenspaceEquiv`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.
-/
def atomicMatrix (w y : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => sqrt (w i) * sqrt (w j) * exp (-|y i-y j|)

omit [Fintype ι] in
/--
Exact identity `inner ℝ (weightedFeature w y i) (weightedFeature w y j) = atomicMatrix w y i
j`.

Use: `chebyshev2.Continuum.atomicOperator_matrix` uses this identity to establish the
identity stated in that declaration.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Use the identities/estimates `chebyshev2.Continuum.feature_inner` with the arguments
shown in the proof.
-/
theorem weightedFeature_inner (w y : ι → ℝ) (i j : ι) :
    inner ℝ (weightedFeature w y i) (weightedFeature w y j) = atomicMatrix w y i j := by
  simp only [weightedFeature,real_inner_smul_left,real_inner_smul_right,feature_inner,atomicMatrix]
  ring

/--
Exact identity `familySynthesis (weightedFeature w y) ∘L (familySynthesis (weightedFeature w
y)).adjoint = atomicOperator w y`.

Use: `chebyshev2.Continuum.atomicEigenspaceEquiv` uses this identity in the displayed
construction of `atomicEigenspaceEquiv`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem atomicOperator_gram (w y : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    familySynthesis (weightedFeature w y) ∘L (familySynthesis (weightedFeature w y)).adjoint = atomicOperator w y := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  rw [familySynthesis_gram]
  apply Finset.sum_congr rfl
  intro i _
  apply ContinuousLinearMap.ext
  intro u
  change inner ℝ (weightedFeature w y i) u • weightedFeature w y i = w i • featureProjection (y i) u
  rw [weightedFeature,real_inner_smul_left,smul_smul]
  simp only [featureProjection,InnerProductSpace.rankOne_apply,smul_smul]
  change (sqrt (w i) * inner ℝ (feature (y i)) u * sqrt (w i)) • feature (y i) =
    (w i * inner ℝ (feature (y i)) u) • feature (y i)
  congr 1
  calc
    _ = sqrt (w i)^2 * inner ℝ (feature (y i)) u := by ring
    _ = _ := by rw [sq_sqrt (hw i)]

/--
Exact identity `LinearMap.toMatrix (EuclideanSpace.basisFun ι ℝ).toBasis
(EuclideanSpace.basisFun ι ℝ).toBasis ((familySynthesis (weightedFeature w y)).adjoint ∘L
familySynthesis (weightedFeature w y)).toLinearMap = atomicMatrix w y`.

Use: `chebyshev2.Continuum.atomicEigenspaceEquiv` uses this identity in the displayed
construction of `atomicEigenspaceEquiv`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem atomicOperator_matrix (w y : ι → ℝ) [DecidableEq ι] :
    LinearMap.toMatrix (EuclideanSpace.basisFun ι ℝ).toBasis (EuclideanSpace.basisFun ι ℝ).toBasis
      ((familySynthesis (weightedFeature w y)).adjoint ∘L familySynthesis (weightedFeature w y)).toLinearMap =
        atomicMatrix w y := by
  rw [familySynthesis_matrix]
  exact funext (fun i => funext (fun j => weightedFeature_inner w y i j))

/--
Atomic and matrix eigenspaces agree at every nonzero eigenvalue.

Use: a standalone supporting definition for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 2.3.

Proof: Use the identities/estimates `chebyshev2.Continuum.atomicOperator_gram` with the
arguments shown in the proof.
-/
def atomicEigenspaceEquiv (w y : ι → ℝ) (hw : ∀ i, 0 ≤ w i) [DecidableEq ι]
    {μ : ℝ} (hμ : μ ≠ 0) :
    Module.End.eigenspace (atomicOperator w y).toLinearMap μ ≃ₗ[ℝ]
      Module.End.eigenspace (Matrix.toEuclideanLin (atomicMatrix w y)) μ := by
  -- Use the identities/estimates `chebyshev2.Continuum.atomicOperator_gram` with the
  -- arguments shown in the proof.
  have hA := atomicOperator_gram w y hw
  have hB : ((familySynthesis (weightedFeature w y)).adjoint ∘L
      familySynthesis (weightedFeature w y)).toLinearMap = Matrix.toEuclideanLin (atomicMatrix w y) := by
    rw [← atomicOperator_matrix w y]
    exact ((LinearMap.toMatrix (EuclideanSpace.basisFun ι ℝ).toBasis
      (EuclideanSpace.basisFun ι ℝ).toBasis).symm_apply_apply _).symm
  rw [← hB,← hA]
  exact gramEigenspaceEquiv _ _ hμ

end
end chebyshev2.Continuum
