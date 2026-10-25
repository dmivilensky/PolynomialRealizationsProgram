import chebyshev2.Green.TraceSquare
import chebyshev1.SineJacobi.SpectralMeasure

/-!
Article: chebyshev2, Theorem 2.3.
Lemma 1 with multiplicities: the actual Green characteristic polynomial.
Use: `chebyshev2.Jacobi.normalizedGreenValue_eq` feeds
`chebyshev2.Continuum.finiteEigenvalue_square_sum` (finite Eigenvalue square sum).
Proof chain: `chebyshev2.Packing.packed_spectral_distance` — chebyshev2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
-/
namespace chebyshev2.Jacobi
noncomputable section
open chebyshev1 Polynomial Real
open scoped BigOperators
variable {N : ℕ} (J : Jacobi N)

/--
Defines `basis` of type `SpectralBasis J.matrix` by `SpectralBasis.ofHermitian _
J.matrix_isHermitian`.

Use: `chebyshev2.Jacobi.green_charpoly` uses this definition to establish the identity
`J.green.charpoly = ∏ j : Fin N, (X-C ((1-chebyshev1.SineJacobi.node N j)⁻¹))`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.green_spectrum`.
-/
def basis : SpectralBasis J.matrix := SpectralBasis.ofHermitian _ J.matrix_isHermitian

/--
Reuse the already proved half-grid enumeration from chebyshev1 for every matrix in the fiber:
mathlib's Hermitian eigenvalues depend only on the characteristic polynomial.

Exact identity `J.basis.eigenvalues = (chebyshev1.SineJacobi.basis N).eigenvalues`.

Use: `chebyshev2.Jacobi.eigenvalue_nodeIndex` rewrites with this identity to establish
exact identity `J.basis.eigenvalues (chebyshev1.SineJacobi.nodeIndex N hN j) =
chebyshev1.SineJacobi.node N j`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.green_spectrum`.

Proof: Use the identities/estimates `chebyshev2.Jacobi.matrix_isHermitian`,
`chebyshev1.JacobiData.matrix_isHermitian`, `chebyshev2.Jacobi.charpoly_eq` with the
arguments shown in the proof.
-/
theorem basis_eigenvalues_eq_sine (hN : 0 < N) (ht : J.Terminal) :
    J.basis.eigenvalues = (chebyshev1.SineJacobi.basis N).eigenvalues := by
  -- Use the identities/estimates `chebyshev2.Jacobi.matrix_isHermitian`,
  -- `chebyshev1.JacobiData.matrix_isHermitian`, `chebyshev2.Jacobi.charpoly_eq` with
  -- the arguments shown in the proof.
  apply (J.matrix_isHermitian.eigenvalues_eq_eigenvalues_iff
    ((chebyshev1.SineJacobi.data N).matrix_isHermitian 0 N)).mpr
  rw [J.charpoly_eq ht, ← chebyshev1.JacobiData.block_eq_charpoly _
    (chebyshev1.SineJacobi.data_aSq_nonneg N)]
  exact (fiberPolynomial_eq N hN).trans (chebyshev1.SineJacobi.terminal N hN).symm

/--
Exact identity `J.basis.eigenvalues (chebyshev1.SineJacobi.nodeIndex N hN j) =
chebyshev1.SineJacobi.node N j`.

Use: `chebyshev2.Jacobi.green_charpoly` rewrites with this identity to establish exact
identity `J.green.charpoly = ∏ j : Fin N, (X-C ((1-chebyshev1.SineJacobi.node N j)⁻¹))`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.green_spectrum`.

Proof: Use the identities/estimates `chebyshev2.Jacobi.basis_eigenvalues_eq_sine`,
`chebyshev1.SineJacobi.eigenvalue_nodeIndex` with the arguments shown in the proof.
-/
theorem eigenvalue_nodeIndex (hN : 0 < N) (ht : J.Terminal) (j : Fin N) :
    J.basis.eigenvalues (chebyshev1.SineJacobi.nodeIndex N hN j) = chebyshev1.SineJacobi.node N j := by
  rw [J.basis_eigenvalues_eq_sine hN ht]
  exact chebyshev1.SineJacobi.eigenvalue_nodeIndex N hN j

/--
The stated quantitative bound `J.basis.eigenvalues i < 1`.

Use: `chebyshev2.Jacobi.green_coordinates` uses this bound to establish the identity
`J.basis.coordinates J.green = Matrix.diagonal (fun i => (1-J.basis.eigenvalues i)⁻¹)`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.green_spectrum`.

Proof: Use the identities/estimates `chebyshev2.Jacobi.matrix_isHermitian`,
`chebyshev2.Jacobi.spectrum_subset_open` with the arguments shown in the proof.
-/
theorem basis_eigenvalues_lt_one (hN : 0 < N) (ht : J.Terminal) (i : Fin N) :
    J.basis.eigenvalues i < 1 :=
  (J.spectrum_subset_open hN ht (J.matrix_isHermitian.eigenvalues_mem_spectrum_real i)).2

/--
Exact identity `J.basis.coordinates J.green = Matrix.diagonal (fun i => (1-J.basis.eigenvalues
i)⁻¹)`.

Use: `chebyshev2.Jacobi.green_charpoly` rewrites with this identity to establish exact
identity `J.green.charpoly = ∏ j : Fin N, (X-C ((1-chebyshev1.SineJacobi.node N j)⁻¹))`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.green_spectrum`.

Proof: Use the identities/estimates `chebyshev2.SpectralCoordinates.coordinates_resolvent`,
`chebyshev2.Jacobi.basis_eigenvalues_lt_one` with the arguments shown in the proof.
-/
theorem green_coordinates (hN : 0 < N) (ht : J.Terminal) :
    J.basis.coordinates J.green = Matrix.diagonal (fun i => (1-J.basis.eigenvalues i)⁻¹) :=
  SpectralCoordinates.coordinates_resolvent J.basis
    (fun i => (sub_pos.mpr (J.basis_eigenvalues_lt_one hN ht i)).ne')

/--
Lemma 1 with multiplicities: the actual Green characteristic polynomial.

Exact identity `J.green.charpoly = ∏ j : Fin N, (X-C ((1-chebyshev1.SineJacobi.node N
j)⁻¹))`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 2.3.

Proof: Use the identities/estimates `chebyshev2.Jacobi.matrix_isHermitian`,
`chebyshev2.SpectralCoordinates.ofHermitian_charpoly`,
`chebyshev2.Jacobi.green_coordinates` with the arguments shown in the proof.
-/
theorem green_charpoly (hN : 0 < N) (ht : J.Terminal) :
    J.green.charpoly = ∏ j : Fin N,
      (X-C ((1-chebyshev1.SineJacobi.node N j)⁻¹)) := by
  -- Use the identities/estimates `chebyshev2.Jacobi.matrix_isHermitian`,
  -- `chebyshev2.SpectralCoordinates.ofHermitian_charpoly`,
  -- `chebyshev2.Jacobi.green_coordinates` with the arguments shown in the proof.
  rw [← SpectralCoordinates.ofHermitian_charpoly J.matrix_isHermitian J.green]
  change (J.basis.coordinates J.green).charpoly = _
  rw [J.green_coordinates hN ht, Matrix.charpoly_diagonal]
  rw [← (chebyshev1.SineJacobi.nodeIndex N hN).prod_comp]
  simp only [J.eigenvalue_nodeIndex hN ht]

/--
Exact identity `spectrum ℝ J.green = Set.range (fun j : Fin N =>
(1-chebyshev1.SineJacobi.node N j)⁻¹)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Theorem A.1.

Proof: Use the identities/estimates `chebyshev2.Jacobi.matrix_isHermitian`,
`chebyshev2.SpectralCoordinates.ofHermitian_spectrum`,
`chebyshev2.Jacobi.green_coordinates` with the arguments shown in the proof.
-/
theorem green_spectrum (hN : 0 < N) (ht : J.Terminal) :
    spectrum ℝ J.green = Set.range (fun j : Fin N => (1-chebyshev1.SineJacobi.node N j)⁻¹) := by
  -- Use the identities/estimates `chebyshev2.Jacobi.matrix_isHermitian`,
  -- `chebyshev2.SpectralCoordinates.ofHermitian_spectrum`,
  -- `chebyshev2.Jacobi.green_coordinates` with the arguments shown in the proof.
  rw [← SpectralCoordinates.ofHermitian_spectrum J.matrix_isHermitian J.green]
  change spectrum ℝ (J.basis.coordinates J.green) = _
  rw [J.green_coordinates hN ht, spectrum_diagonal]
  ext x
  constructor
  · rintro ⟨i,hi⟩
    refine ⟨(chebyshev1.SineJacobi.nodeIndex N hN).symm i, ?_⟩
    dsimp only
    rw [← J.eigenvalue_nodeIndex hN ht, Equiv.apply_symm_apply]
    exact hi
  · rintro ⟨j,hj⟩
    refine ⟨chebyshev1.SineJacobi.nodeIndex N hN j, ?_⟩
    dsimp only
    rw [J.eigenvalue_nodeIndex hN ht]
    exact hj

/--
Defines `normalizedGreenValue` of type `ℝ` by `1/(2*(N:ℝ)^2*sin
((2*(j:ℝ)+1)*Real.pi/(4*(N:ℝ)))^2)`.

Use: `chebyshev2.Jacobi.normalizedGreenValue_eq` uses this definition to establish exact
identity `normalizedGreenValue N j = (1-chebyshev1.SineJacobi.node N j)⁻¹/(N:ℝ)^2`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.
-/
def normalizedGreenValue (N : ℕ) (j : Fin N) : ℝ :=
  1/(2*(N:ℝ)^2*sin ((2*(j:ℝ)+1)*Real.pi/(4*(N:ℝ)))^2)

/--
Exact identity `normalizedGreenValue N j = (1-chebyshev1.SineJacobi.node N j)⁻¹/(N:ℝ)^2`.

Use: `chebyshev2.Continuum.finiteEigenvalue_square_sum` rewrites with this identity to
establish exact identity `(∑ j : Fin N, finiteEigenvalue N j ^ 2) = 2 / 3 + 1 / (3 * (N :
ℝ)^2)`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem normalizedGreenValue_eq (j : Fin N) :
    normalizedGreenValue N j = (1-chebyshev1.SineJacobi.node N j)⁻¹/(N:ℝ)^2 := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  let θ := (2*(j:ℝ)+1)*Real.pi/(4*(N:ℝ))
  have hc : 1-chebyshev1.SineJacobi.node N j = 2*sin θ^2 := by
    unfold chebyshev1.SineJacobi.node chebyshev1.SineJacobi.nodeAngle
    rw [show (2*(j:ℝ)+1)*Real.pi/(2*(N:ℝ)) = 2*θ by dsimp [θ]; ring, cos_two_mul']
    nlinarith [sin_sq_add_cos_sq θ]
  rw [hc]
  unfold normalizedGreenValue
  change 1/(2*(N:ℝ)^2*sin θ^2) = (2*sin θ^2)⁻¹/(N:ℝ)^2
  simp only [mul_inv_rev, div_eq_mul_inv]; ring

end
end chebyshev2.Jacobi
