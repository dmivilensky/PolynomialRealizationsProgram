import chebyshev2.Packing.Coupling
import chebyshev2.Packing.Jacobi
import chebyshev2.Continuum.SpectralPerturbation
import chebyshev2.Continuum.SpectralIdentification
import chebyshev2.Continuum.AtomicSpectrum
import chebyshev2.Continuum.GreenEigenvalues

/-!
Article: chebyshev2, Theorem 2.3.
Theorem 2.3 in the irreducible fiber, with the stronger error 2/sqrt(N).
Use: `chebyshev2.Packing.Jacobi.atomicWeight_pos` feeds
`chebyshev2.Packing.Representation.atomic_matrix_traceBound` (atomic matrix trace Bound).
Proof chain: `chebyshev2.Packing.packed_spectral_distance` — chebyshev2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
-/
namespace chebyshev2.Packing.Jacobi
noncomputable section
open chebyshev2.Continuum MeasureTheory Real Set
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

variable {N : ℕ} (J : chebyshev2.Jacobi N)

/--
Defines `atomicWeight` of type `ℝ` by `J.green i i / (N : ℝ)^2`.

Use: `chebyshev2.Packing.Jacobi.blocks_weight` uses this definition to establish exact
identity `(blocks J hN ht hir).height i^2 * ((blocks J hN ht hir).right i-(blocks J hN ht
hir).left i) = atomicWeight J i`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.
-/
def atomicWeight (i : Fin N) : ℝ := J.green i i / (N : ℝ)^2

/--
The stated quantitative bound `0 < atomicWeight J i`.

Use: `chebyshev2.Packing.Jacobi.density_atomic_spectral_distance` uses this bound to
establish the bound stated in that declaration.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Use the identities/estimates `chebyshev2.Jacobi.green_diagonal_pos` with the
arguments shown in the proof.
-/
theorem atomicWeight_pos (hN : 0 < N) (ht : J.Terminal) (i : Fin N) : 0 < atomicWeight J i :=
  div_pos (J.green_diagonal_pos hN ht i) (pow_pos (Nat.cast_pos.mpr hN) 2)

/--
Exact identity `(blocks J hN ht hir).height i^2 * ((blocks J hN ht hir).right i-(blocks J hN ht
hir).left i) = atomicWeight J i`.

Use: `chebyshev2.Packing.Jacobi.density_atomic_traceBound` rewrites with this identity to
establish the precise assertion is `TraceBound (densityOperator (density J hN ht hir) -
atomicOperator (atomicWeight J) (J.representationPoint hN)) (2 / sqrt (N : ℝ))`.

Article: chebyshev2, Theorem 2.3.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem blocks_weight (hN : 0 < N) (ht : J.Terminal) (hir : J.Irreducible) (i : Fin N) :
    (blocks J hN ht hir).height i^2 * ((blocks J hN ht hir).right i-(blocks J hN ht hir).left i) =
      atomicWeight J i := by
  change (J.green i i/N)^2 * (J.intervalRight hN i-J.intervalLeft hN i) = _
  rw [J.interval_length]
  unfold atomicWeight
  field_simp [(J.green_diagonal_pos hN ht i).ne']

/--
The explicit coupling has the article's cost 1/(2N).

The stated quantitative bound `(∫ z, |z.1-z.2| ∂(blocks J hN ht hir).coupling
(J.representationPoint hN)) ≤ 1/(2*(N : ℝ))`.

Use: `chebyshev2.Packing.Jacobi.density_atomic_traceBound` uses this bound to establish the
precise assertion is `TraceBound (densityOperator (density J hN ht hir) - atomicOperator
(atomicWeight J) (J.representationPoint hN)) (2 / sqrt (N : ℝ))`.

Article: chebyshev2, Theorem 2.3.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem coupling_cost_bound (hN : 0 < N) (ht : J.Terminal) (hir : J.Irreducible) :
    (∫ z, |z.1-z.2| ∂(blocks J hN ht hir).coupling (J.representationPoint hN)) ≤ 1/(2*(N : ℝ)) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hc := J.contractive_of_pencils (J.one_sub_posDef hN ht) (J.one_add_posDef hN ht)
  have h := (blocks J hN ht hir).coupling_cost (J.representationPoint hN)
    (J.representationPoint_mem_interval hN hc hir)
  have he (i : Fin N) : (blocks J hN ht hir).height i^2 *
      ((blocks J hN ht hir).right i-(blocks J hN ht hir).left i)^2/2 = 1/(2*(N : ℝ)^2) := by
    change (J.green i i/N)^2 * (J.intervalRight hN i-J.intervalLeft hN i)^2/2 = _
    rw [J.interval_length]
    field_simp [(J.green_diagonal_pos hN ht i).ne',Nat.cast_ne_zero.mpr hN.ne']
  simp_rw [he] at h
  have hs : (∑ _i : Fin N, 1/(2*(N : ℝ)^2)) = 1/(2*(N : ℝ)) := by
    simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul]
    field_simp
  exact h.trans_eq hs

/--
The actual density feature operator is within 2/sqrt(N) of its atomic one.

The precise assertion is `TraceBound (densityOperator (density J hN ht hir) - atomicOperator
(atomicWeight J) (J.representationPoint hN)) (2 / sqrt (N : ℝ))`.

Use: `chebyshev2.Packing.Jacobi.density_atomic_spectral_distance` uses this assertion to
establish the bound stated in that declaration.

Article: chebyshev2, Theorem 2.3.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem density_atomic_traceBound (hN : 0 < N) (ht : J.Terminal) (hir : J.Irreducible) :
    TraceBound (densityOperator (density J hN ht hir) -
      atomicOperator (atomicWeight J) (J.representationPoint hN)) (2 / sqrt (N : ℝ)) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have h := (blocks J hN ht hir).density_atomic_transport (J.representationPoint hN)
  simp_rw [blocks_weight J hN ht hir] at h
  change TraceBound (densityOperator (density J hN ht hir)-_) _ at h
  have hm : (∫ x, (blocks J hN ht hir).closedDensity x) = 1 := density_mass J hN ht hir
  rw [hm] at h
  apply h.mono
  have hcost := coupling_cost_bound J hN ht hir
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have he : 2 * sqrt (2 * 1 * (1/(2*(N : ℝ)))) = 2/sqrt (N : ℝ) := by
    rw [show 2 * 1 * (1/(2*(N : ℝ))) = (N : ℝ)⁻¹ by field_simp]
    rw [sqrt_inv,div_eq_mul_inv]
  rw [← he]
  apply mul_le_mul_of_nonneg_left (sqrt_le_sqrt ?_) (by norm_num)
  nlinarith

/--
In one irreducible block there is no atomic matrix error.

Exact identity `atomicMatrix (atomicWeight J) (J.representationPoint hN) = J.normalizedGreen`.

Use: `chebyshev2.Packing.Jacobi.packing_spectral_distance` uses this identity to establish
the stated quantitative bound `(∑' j, |kernelEigenvalue (blocks J hN ht
hir).closedDensity_integrable (blocks J hN ht hir).closedDensity_nonneg j - finiteEigenvalue N
j|) ≤ 2/sqrt (N : ℝ)`.

Article: chebyshev2, Theorem 2.3.

Proof: Use the identities/estimates `chebyshev2.Jacobi.contractive_of_pencils`,
`chebyshev2.Jacobi.one_sub_posDef`, `chebyshev2.Jacobi.one_add_posDef` with the
arguments shown in the proof.
-/
theorem atomicMatrix_eq_normalizedGreen (hN : 0 < N) (ht : J.Terminal) (hir : J.Irreducible) :
    atomicMatrix (atomicWeight J) (J.representationPoint hN) = J.normalizedGreen := by
  -- Use the identities/estimates `chebyshev2.Jacobi.contractive_of_pencils`,
  -- `chebyshev2.Jacobi.one_sub_posDef`, `chebyshev2.Jacobi.one_add_posDef` with the
  -- arguments shown in the proof.
  ext i j
  have hc := J.contractive_of_pencils (J.one_sub_posDef hN ht) (J.one_add_posDef hN ht)
  have hi := J.green_diagonal_pos hN ht i
  have hj := J.green_diagonal_pos hN ht j
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  change sqrt (J.green i i/(N : ℝ)^2) * sqrt (J.green j j/(N : ℝ)^2) *
      exp (-|J.representationPoint hN i-J.representationPoint hN j|) = ((N : ℝ)^2)⁻¹ * J.green i j
  rw [J.green_representation hN hc hir i j,sqrt_div hi.le,sqrt_div hj.le,sqrt_sq hn.le]
  rw [sqrt_mul hi.le]
  ring

/--
Spectral transfer for the irreducible packing, at the level of actual continuum and atomic
operators.

The stated quantitative bound `(∑' j, |kernelEigenvalue (blocks J hN ht
hir).closedDensity_integrable (blocks J hN ht hir).closedDensity_nonneg j -
(atomicMatrixSpectralData (atomicWeight J) (J.representationPoint hN)).eigenvalue j|) ≤ 2/sqrt
(N : ℝ)`.

Use: `chebyshev2.Packing.Jacobi.packing_spectral_distance` uses this bound to establish the
stated quantitative bound `(∑' j, |kernelEigenvalue (blocks J hN ht
hir).closedDensity_integrable (blocks J hN ht hir).closedDensity_nonneg j - finiteEigenvalue N
j|) ≤ 2/sqrt (N : ℝ)`.

Article: chebyshev2, Theorem 2.3.

Proof: Use the identities/estimates `chebyshev2.Packing.Blocks.closedDensity_integrable`,
`chebyshev2.Packing.Blocks.closedDensity_nonneg`,
`chebyshev2.Packing.Jacobi.atomicWeight_pos` with the arguments shown in the proof.
-/
theorem density_atomic_spectral_distance (hN : 0 < N) (ht : J.Terminal) (hir : J.Irreducible) :
    (∑' j, |kernelEigenvalue (blocks J hN ht hir).closedDensity_integrable
        (blocks J hN ht hir).closedDensity_nonneg j -
      (atomicMatrixSpectralData (atomicWeight J) (J.representationPoint hN)).eigenvalue j|) ≤
        2/sqrt (N : ℝ) := by
  -- Use the identities/estimates `chebyshev2.Packing.Blocks.closedDensity_integrable`,
  -- `chebyshev2.Packing.Blocks.closedDensity_nonneg`,
  -- `chebyshev2.Packing.Jacobi.atomicWeight_pos` with the arguments shown in the proof.
  let B := blocks J hN ht hir
  let hm := B.closedDensity_integrable
  let hn := B.closedDensity_nonneg
  let hw := fun i => (atomicWeight_pos J hN ht i).le
  have h := eigenvalue_l1_le_traceBound (densityOperator_isCompact hm)
    (atomicOperator_isCompact _ _ hw) (densityOperator_positive hm hn)
    (atomicOperator_positive _ _ hw) (densitySpectralData hm hn)
    (atomicSpectralData _ _ hw) (density_atomic_traceBound J hN ht hir)
  rwa [density_kernel_eigenvalue_eq hm hn,atomic_matrix_eigenvalue_eq] at h

/--
Theorem 2.3 in the irreducible fiber, with the stronger error 2/sqrt(N).

The stated quantitative bound `(∑' j, |kernelEigenvalue (blocks J hN ht
hir).closedDensity_integrable (blocks J hN ht hir).closedDensity_nonneg j - finiteEigenvalue N
j|) ≤ 2/sqrt (N : ℝ)`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 2.3.

Proof: Use the identities/estimates
`chebyshev2.Packing.Jacobi.density_atomic_spectral_distance`,
`chebyshev2.Continuum.eigenvalue_eq_of_operator_eq`,
`chebyshev2.Packing.Jacobi.atomicMatrix_eq_normalizedGreen` with the arguments shown in the
proof.
-/
theorem packing_spectral_distance (hN : 0 < N) (ht : J.Terminal) (hir : J.Irreducible) :
    (∑' j, |kernelEigenvalue (blocks J hN ht hir).closedDensity_integrable
        (blocks J hN ht hir).closedDensity_nonneg j - finiteEigenvalue N j|) ≤ 2/sqrt (N : ℝ) := by
  -- Use the identities/estimates
  -- `chebyshev2.Packing.Jacobi.density_atomic_spectral_distance`,
  -- `chebyshev2.Continuum.eigenvalue_eq_of_operator_eq`,
  -- `chebyshev2.Packing.Jacobi.atomicMatrix_eq_normalizedGreen` with the arguments shown
  -- in the proof.
  have h := density_atomic_spectral_distance J hN ht hir
  have he : (atomicMatrixSpectralData (atomicWeight J) (J.representationPoint hN)).eigenvalue =
      finiteEigenvalue N := by
    have hb := eigenvalue_eq_of_operator_eq
      (congrArg (Matrix.toEuclideanCLM (𝕜 := ℝ)) (atomicMatrix_eq_normalizedGreen J hN ht hir))
      (atomicMatrixSpectralData (atomicWeight J) (J.representationPoint hN)) (greenSpectralData J hN ht)
    exact hb.trans (green_eigenvalue_eq J hN ht)
  rwa [he] at h

end
end chebyshev2.Packing.Jacobi
