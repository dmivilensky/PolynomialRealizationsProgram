import «2610.05164v2».Green.TraceSquare
import «2606.16671v2».SineJacobi.SpectralMeasure

/-!
Article: 2610.05164v2, Theorem 2.3.
Lemma 1 with multiplicities: the actual Green characteristic polynomial.
Use: `«2610.05164v2».Jacobi.normalizedGreenValue_eq` feeds
`«2610.05164v2».Continuum.finiteEigenvalue_square_sum` (finite Eigenvalue square sum).
Proof chain: `«2610.05164v2».Packing.packed_spectral_distance` — 2610.05164v2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
-/
namespace «2610.05164v2».Jacobi
noncomputable section
open «2606.16671v2» Polynomial Real
open scoped BigOperators
variable {N : ℕ} (J : Jacobi N)

/--
Defines `basis` of type `SpectralBasis J.matrix` by `SpectralBasis.ofHermitian _
J.matrix_isHermitian`.

Use: `«2610.05164v2».Jacobi.green_charpoly` uses this definition to establish the identity
`J.green.charpoly = ∏ j : Fin N, (X-C ((1-«2606.16671v2».SineJacobi.node N j)⁻¹))`.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».Jacobi.green_spectrum`.
-/
def basis : SpectralBasis J.matrix := SpectralBasis.ofHermitian _ J.matrix_isHermitian

/--
Reuse the already proved half-grid enumeration from 2606.16671v2 for every matrix in the fiber:
mathlib's Hermitian eigenvalues depend only on the characteristic polynomial.

Exact identity `J.basis.eigenvalues = («2606.16671v2».SineJacobi.basis N).eigenvalues`.

Use: `«2610.05164v2».Jacobi.eigenvalue_nodeIndex` rewrites with this identity to establish
exact identity `J.basis.eigenvalues («2606.16671v2».SineJacobi.nodeIndex N hN j) =
«2606.16671v2».SineJacobi.node N j`.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».Jacobi.green_spectrum`.

Proof: Use the identities/estimates `«2610.05164v2».Jacobi.matrix_isHermitian`,
`«2606.16671v2».JacobiData.matrix_isHermitian`, `«2610.05164v2».Jacobi.charpoly_eq` with the
arguments shown in the proof.
-/
theorem basis_eigenvalues_eq_sine (hN : 0 < N) (ht : J.Terminal) :
    J.basis.eigenvalues = («2606.16671v2».SineJacobi.basis N).eigenvalues := by
  -- Use the identities/estimates `«2610.05164v2».Jacobi.matrix_isHermitian`,
  -- `«2606.16671v2».JacobiData.matrix_isHermitian`, `«2610.05164v2».Jacobi.charpoly_eq` with
  -- the arguments shown in the proof.
  apply (J.matrix_isHermitian.eigenvalues_eq_eigenvalues_iff
    ((«2606.16671v2».SineJacobi.data N).matrix_isHermitian 0 N)).mpr
  rw [J.charpoly_eq ht, ← «2606.16671v2».JacobiData.block_eq_charpoly _
    («2606.16671v2».SineJacobi.data_aSq_nonneg N)]
  exact (fiberPolynomial_eq N hN).trans («2606.16671v2».SineJacobi.terminal N hN).symm

/--
Exact identity `J.basis.eigenvalues («2606.16671v2».SineJacobi.nodeIndex N hN j) =
«2606.16671v2».SineJacobi.node N j`.

Use: `«2610.05164v2».Jacobi.green_charpoly` rewrites with this identity to establish exact
identity `J.green.charpoly = ∏ j : Fin N, (X-C ((1-«2606.16671v2».SineJacobi.node N j)⁻¹))`.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».Jacobi.green_spectrum`.

Proof: Use the identities/estimates `«2610.05164v2».Jacobi.basis_eigenvalues_eq_sine`,
`«2606.16671v2».SineJacobi.eigenvalue_nodeIndex` with the arguments shown in the proof.
-/
theorem eigenvalue_nodeIndex (hN : 0 < N) (ht : J.Terminal) (j : Fin N) :
    J.basis.eigenvalues («2606.16671v2».SineJacobi.nodeIndex N hN j) = «2606.16671v2».SineJacobi.node N j := by
  rw [J.basis_eigenvalues_eq_sine hN ht]
  exact «2606.16671v2».SineJacobi.eigenvalue_nodeIndex N hN j

/--
The stated quantitative bound `J.basis.eigenvalues i < 1`.

Use: `«2610.05164v2».Jacobi.green_coordinates` uses this bound to establish the identity
`J.basis.coordinates J.green = Matrix.diagonal (fun i => (1-J.basis.eigenvalues i)⁻¹)`.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».Jacobi.green_spectrum`.

Proof: Use the identities/estimates `«2610.05164v2».Jacobi.matrix_isHermitian`,
`«2610.05164v2».Jacobi.spectrum_subset_open` with the arguments shown in the proof.
-/
theorem basis_eigenvalues_lt_one (hN : 0 < N) (ht : J.Terminal) (i : Fin N) :
    J.basis.eigenvalues i < 1 :=
  (J.spectrum_subset_open hN ht (J.matrix_isHermitian.eigenvalues_mem_spectrum_real i)).2

/--
Exact identity `J.basis.coordinates J.green = Matrix.diagonal (fun i => (1-J.basis.eigenvalues
i)⁻¹)`.

Use: `«2610.05164v2».Jacobi.green_charpoly` rewrites with this identity to establish exact
identity `J.green.charpoly = ∏ j : Fin N, (X-C ((1-«2606.16671v2».SineJacobi.node N j)⁻¹))`.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».Jacobi.green_spectrum`.

Proof: Use the identities/estimates `«2610.05164v2».SpectralCoordinates.coordinates_resolvent`,
`«2610.05164v2».Jacobi.basis_eigenvalues_lt_one` with the arguments shown in the proof.
-/
theorem green_coordinates (hN : 0 < N) (ht : J.Terminal) :
    J.basis.coordinates J.green = Matrix.diagonal (fun i => (1-J.basis.eigenvalues i)⁻¹) :=
  SpectralCoordinates.coordinates_resolvent J.basis
    (fun i => (sub_pos.mpr (J.basis_eigenvalues_lt_one hN ht i)).ne')

/--
Lemma 1 with multiplicities: the actual Green characteristic polynomial.

Exact identity `J.green.charpoly = ∏ j : Fin N, (X-C ((1-«2606.16671v2».SineJacobi.node N
j)⁻¹))`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 2.3.

Proof: Use the identities/estimates `«2610.05164v2».Jacobi.matrix_isHermitian`,
`«2610.05164v2».SpectralCoordinates.ofHermitian_charpoly`,
`«2610.05164v2».Jacobi.green_coordinates` with the arguments shown in the proof.
-/
theorem green_charpoly (hN : 0 < N) (ht : J.Terminal) :
    J.green.charpoly = ∏ j : Fin N,
      (X-C ((1-«2606.16671v2».SineJacobi.node N j)⁻¹)) := by
  -- Use the identities/estimates `«2610.05164v2».Jacobi.matrix_isHermitian`,
  -- `«2610.05164v2».SpectralCoordinates.ofHermitian_charpoly`,
  -- `«2610.05164v2».Jacobi.green_coordinates` with the arguments shown in the proof.
  rw [← SpectralCoordinates.ofHermitian_charpoly J.matrix_isHermitian J.green]
  change (J.basis.coordinates J.green).charpoly = _
  rw [J.green_coordinates hN ht, Matrix.charpoly_diagonal]
  rw [← («2606.16671v2».SineJacobi.nodeIndex N hN).prod_comp]
  simp only [J.eigenvalue_nodeIndex hN ht]

/--
Exact identity `spectrum ℝ J.green = Set.range (fun j : Fin N =>
(1-«2606.16671v2».SineJacobi.node N j)⁻¹)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Theorem A.1.

Proof: Use the identities/estimates `«2610.05164v2».Jacobi.matrix_isHermitian`,
`«2610.05164v2».SpectralCoordinates.ofHermitian_spectrum`,
`«2610.05164v2».Jacobi.green_coordinates` with the arguments shown in the proof.
-/
theorem green_spectrum (hN : 0 < N) (ht : J.Terminal) :
    spectrum ℝ J.green = Set.range (fun j : Fin N => (1-«2606.16671v2».SineJacobi.node N j)⁻¹) := by
  -- Use the identities/estimates `«2610.05164v2».Jacobi.matrix_isHermitian`,
  -- `«2610.05164v2».SpectralCoordinates.ofHermitian_spectrum`,
  -- `«2610.05164v2».Jacobi.green_coordinates` with the arguments shown in the proof.
  rw [← SpectralCoordinates.ofHermitian_spectrum J.matrix_isHermitian J.green]
  change spectrum ℝ (J.basis.coordinates J.green) = _
  rw [J.green_coordinates hN ht, spectrum_diagonal]
  ext x
  constructor
  · rintro ⟨i,hi⟩
    refine ⟨(«2606.16671v2».SineJacobi.nodeIndex N hN).symm i, ?_⟩
    dsimp only
    rw [← J.eigenvalue_nodeIndex hN ht, Equiv.apply_symm_apply]
    exact hi
  · rintro ⟨j,hj⟩
    refine ⟨«2606.16671v2».SineJacobi.nodeIndex N hN j, ?_⟩
    dsimp only
    rw [J.eigenvalue_nodeIndex hN ht]
    exact hj

/--
Defines `normalizedGreenValue` of type `ℝ` by `1/(2*(N:ℝ)^2*sin
((2*(j:ℝ)+1)*Real.pi/(4*(N:ℝ)))^2)`.

Use: `«2610.05164v2».Jacobi.normalizedGreenValue_eq` uses this definition to establish exact
identity `normalizedGreenValue N j = (1-«2606.16671v2».SineJacobi.node N j)⁻¹/(N:ℝ)^2`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.
-/
def normalizedGreenValue (N : ℕ) (j : Fin N) : ℝ :=
  1/(2*(N:ℝ)^2*sin ((2*(j:ℝ)+1)*Real.pi/(4*(N:ℝ)))^2)

/--
Exact identity `normalizedGreenValue N j = (1-«2606.16671v2».SineJacobi.node N j)⁻¹/(N:ℝ)^2`.

Use: `«2610.05164v2».Continuum.finiteEigenvalue_square_sum` rewrites with this identity to
establish exact identity `(∑ j : Fin N, finiteEigenvalue N j ^ 2) = 2 / 3 + 1 / (3 * (N :
ℝ)^2)`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem normalizedGreenValue_eq (j : Fin N) :
    normalizedGreenValue N j = (1-«2606.16671v2».SineJacobi.node N j)⁻¹/(N:ℝ)^2 := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  let θ := (2*(j:ℝ)+1)*Real.pi/(4*(N:ℝ))
  have hc : 1-«2606.16671v2».SineJacobi.node N j = 2*sin θ^2 := by
    unfold «2606.16671v2».SineJacobi.node «2606.16671v2».SineJacobi.nodeAngle
    rw [show (2*(j:ℝ)+1)*Real.pi/(2*(N:ℝ)) = 2*θ by dsimp [θ]; ring, cos_two_mul']
    nlinarith [sin_sq_add_cos_sq θ]
  rw [hc]
  unfold normalizedGreenValue
  change 1/(2*(N:ℝ)^2*sin θ^2) = (2*sin θ^2)⁻¹/(N:ℝ)^2
  simp only [mul_inv_rev, div_eq_mul_inv]; ring

end
end «2610.05164v2».Jacobi
