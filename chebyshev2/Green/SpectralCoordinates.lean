import chebyshev2.Green.Positivity
import chebyshev1.Spectral.Basis

/-!
Article: chebyshev2, Theorem A.1.
Spectral Coordinates.
Use: `chebyshev2.SpectralCoordinates.trace_resolvent_square` feeds
`chebyshev2.Jacobi.green_trace_square_logDerivative` (A resolvent trace identity obtained by
differentiating the logarithmic derivative of the actual characteristic polynomial).
Proof chain: `chebyshev2.Jacobi.green_trace_square` — chebyshev2, Theorem A.1; Centering lift,
contractivity, odd Green entries and characteristic polynomial.
-/
namespace chebyshev2.SpectralCoordinates
noncomputable section
open chebyshev1 Matrix
variable {d : Type*} [Fintype d] [DecidableEq d]
variable {H : Matrix d d ℝ} (B : SpectralBasis H)

/--
Exact identity `B.coordinates 1 = 1`.

Use: `chebyshev2.SpectralCoordinates.coordinates_resolvent` rewrites with this identity to
establish exact identity `B.coordinates (1-H)⁻¹ = Matrix.diagonal (fun i => (1-B.eigenvalues
i)⁻¹)`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.lift_contractive`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem coordinates_one : B.coordinates 1 = 1 := by simp [SpectralBasis.coordinates, B.transpose_mul]

/--
Exact identity `B.coordinates (A-C) = B.coordinates A-B.coordinates C`.

Use: `chebyshev2.SpectralCoordinates.coordinates_resolvent` rewrites with this identity to
establish exact identity `B.coordinates (1-H)⁻¹ = Matrix.diagonal (fun i => (1-B.eigenvalues
i)⁻¹)`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.lift_contractive`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem coordinates_sub (A C : Matrix d d ℝ) :
    B.coordinates (A-C) = B.coordinates A-B.coordinates C := by simp [SpectralBasis.coordinates, Matrix.mul_sub, Matrix.sub_mul]

/--
Exact identity `B.coordinates A⁻¹ = (B.coordinates A)⁻¹`.

Use: `chebyshev2.SpectralCoordinates.coordinates_resolvent` rewrites with this identity to
establish exact identity `B.coordinates (1-H)⁻¹ = Matrix.diagonal (fun i => (1-B.eigenvalues
i)⁻¹)`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.green_spectrum`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem coordinates_inv (A : Matrix d d ℝ) : B.coordinates A⁻¹ = (B.coordinates A)⁻¹ := by
  simp only [SpectralBasis.coordinates, Matrix.mul_inv_rev,
    Matrix.inv_eq_left_inv B.transpose_mul, Matrix.inv_eq_left_inv B.mul_transpose]
  simp [Matrix.mul_assoc]

/--
Exact identity `Matrix.trace (B.coordinates A) = Matrix.trace A`.

Use: `chebyshev2.SpectralCoordinates.trace_resolvent` rewrites with this identity to
establish exact identity `Matrix.trace (1-H)⁻¹ = ∑ i, (1-B.eigenvalues i)⁻¹`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.green_trace_square`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem coordinates_trace (A : Matrix d d ℝ) : Matrix.trace (B.coordinates A) = Matrix.trace A := by rw [SpectralBasis.coordinates, Matrix.trace_mul_cycle, B.mul_transpose, Matrix.one_mul]

/--
Exact identity `spectrum ℝ ((SpectralBasis.ofHermitian H hH).coordinates A) = spectrum ℝ A`.

Use: `chebyshev2.Jacobi.green_spectrum` rewrites with this identity to establish exact
identity `spectrum ℝ J.green = Set.range (fun j : Fin N => (1-chebyshev1.SineJacobi.node N
j)⁻¹)`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.green_spectrum`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem ofHermitian_spectrum (hH : H.IsHermitian) (A : Matrix d d ℝ) :
    spectrum ℝ ((SpectralBasis.ofHermitian H hH).coordinates A) = spectrum ℝ A := by
  simpa [SpectralBasis.coordinates, SpectralBasis.ofHermitian, Unitary.coe_star,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Unitary.spectrum_star_left_conjugate (R := ℝ) (a := A) (U := hH.eigenvectorUnitary))

/--
Exact identity `((SpectralBasis.ofHermitian H hH).coordinates A).charpoly = A.charpoly`.

Use: `chebyshev2.Jacobi.green_charpoly` rewrites with this identity to establish exact
identity `J.green.charpoly = ∏ j : Fin N, (X-C ((1-chebyshev1.SineJacobi.node N j)⁻¹))`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem ofHermitian_charpoly (hH : H.IsHermitian) (A : Matrix d d ℝ) :
    ((SpectralBasis.ofHermitian H hH).coordinates A).charpoly = A.charpoly := by
  let C := SpectralBasis.ofHermitian H hH
  have he := Matrix.charpoly_units_conj' (Unitary.toUnits hH.eigenvectorUnitary) A
  change (C.Q⁻¹*A*C.Q).charpoly = A.charpoly at he
  rw [Matrix.inv_eq_left_inv C.transpose_mul] at he
  exact he

/--
Exact identity `B.coordinates (1-H)⁻¹ = Matrix.diagonal (fun i => (1-B.eigenvalues i)⁻¹)`.

Use: `chebyshev2.SpectralCoordinates.trace_resolvent` rewrites with this identity to
establish exact identity `Matrix.trace (1-H)⁻¹ = ∑ i, (1-B.eigenvalues i)⁻¹`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.green_spectrum`.

Proof: Use the identities/estimates `chebyshev2.SpectralCoordinates.coordinates_inv`,
`chebyshev2.SpectralCoordinates.coordinates_sub`,
`chebyshev2.SpectralCoordinates.coordinates_one` with the arguments shown in the proof.
-/
theorem coordinates_resolvent (h : ∀ i, 1-B.eigenvalues i ≠ 0) : B.coordinates (1-H)⁻¹ =
    Matrix.diagonal (fun i => (1-B.eigenvalues i)⁻¹) := by
  rw [coordinates_inv, coordinates_sub, coordinates_one]
  rw [show B.coordinates H = Matrix.diagonal B.eigenvalues from B.diagonalize]
  rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
  apply Matrix.inv_eq_left_inv
  simp [Matrix.diagonal_mul_diagonal, h]

/--
Exact identity `Matrix.trace (1-H)⁻¹ = ∑ i, (1-B.eigenvalues i)⁻¹`.

Use: `chebyshev2.Continuum.finiteEigenvalue_sum` rewrites with this identity to establish
exact identity `(∑ j : Fin N, finiteEigenvalue N j) = 1`.

Article: chebyshev2, Theorem 2.4 via
`chebyshev2.Continuum.finite_reference_distance_bound`.

Proof: Use the identities/estimates `chebyshev2.SpectralCoordinates.coordinates_trace`,
`chebyshev2.SpectralCoordinates.coordinates_resolvent` with the arguments shown in the
proof.
-/
theorem trace_resolvent (h : ∀ i, 1-B.eigenvalues i ≠ 0) :
    Matrix.trace (1-H)⁻¹ = ∑ i, (1-B.eigenvalues i)⁻¹ := by rw [← coordinates_trace B, coordinates_resolvent B h, Matrix.trace_diagonal]

/--
Exact identity `Matrix.trace ((1-H)⁻¹*(1-H)⁻¹) = ∑ i, (1-B.eigenvalues i)⁻¹^2`.

Use: `chebyshev2.Continuum.finiteEigenvalue_square_sum` rewrites with this identity to
establish exact identity `(∑ j : Fin N, finiteEigenvalue N j ^ 2) = 2 / 3 + 1 / (3 * (N :
ℝ)^2)`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.green_trace_square`.

Proof: Use the identities/estimates `chebyshev2.SpectralCoordinates.coordinates_trace`,
`chebyshev1.SpectralBasis.coordinates_mul`,
`chebyshev2.SpectralCoordinates.coordinates_resolvent` with the arguments shown in the
proof.
-/
theorem trace_resolvent_square (h : ∀ i, 1-B.eigenvalues i ≠ 0) : Matrix.trace ((1-H)⁻¹*(1-H)⁻¹) =
    ∑ i, (1-B.eigenvalues i)⁻¹^2 := by
  rw [← coordinates_trace B, B.coordinates_mul, coordinates_resolvent B h,
    Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  simp only [pow_two]

end
end chebyshev2.SpectralCoordinates
