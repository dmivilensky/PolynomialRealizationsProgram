import chebyshev2.Green.Spectrum

/-!
Article: chebyshev2, Theorem 2.3.
The normalized eigenvalues of Lemma 1 are in strictly decreasing order.
Use: `chebyshev2.Jacobi.normalizedGreenValue_strictAnti` feeds
`chebyshev2.Continuum.green_eigenvalue_eq` (The ordered spectrum extracted from the actual Green
matrix is the explicit finite sequence used in Theorem 2.4).
Proof chain: `chebyshev2.Packing.packed_spectral_distance` — chebyshev2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
-/
namespace chebyshev2.Jacobi
noncomputable section
open chebyshev1 Polynomial Real
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} (J : Jacobi N)

/--
Defines `normalizedGreen` of type `` by `((N:ℝ)^2)⁻¹ • J.green`.

Use: `chebyshev2.Jacobi.normalizedGreen_charpoly` rewrites with this definition to
establish exact identity `J.normalizedGreen.charpoly = ∏ j : Fin N, (X-C (normalizedGreenValue
N j))`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.
-/
def normalizedGreen := ((N:ℝ)^2)⁻¹ • J.green

/--
Exact identity `J.normalizedGreen.charpoly = ∏ j : Fin N, (X-C (normalizedGreenValue N j))`.

Use: `chebyshev2.Continuum.green_eigenvalue_eq` rewrites with this identity to establish
exact identity `(greenSpectralData J hN ht).eigenvalue = finiteEigenvalue N`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem normalizedGreen_charpoly (hN : 0 < N) (ht : J.Terminal) :
    J.normalizedGreen.charpoly = ∏ j : Fin N, (X-C (normalizedGreenValue N j)) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  rw [← SpectralCoordinates.ofHermitian_charpoly J.matrix_isHermitian J.normalizedGreen]
  change (J.basis.coordinates J.normalizedGreen).charpoly = _
  have he : J.basis.coordinates J.normalizedGreen =
      Matrix.diagonal (fun i => (1-J.basis.eigenvalues i)⁻¹/(N:ℝ)^2) := by
    change J.basis.Qᵀ*(((N:ℝ)^2)⁻¹ • J.green)*J.basis.Q = _
    rw [Matrix.mul_smul, Matrix.smul_mul]
    change ((N:ℝ)^2)⁻¹ • J.basis.coordinates J.green = _
    rw [J.green_coordinates hN ht, ← Matrix.diagonal_smul]
    congr 1; funext i; simp [div_eq_mul_inv,mul_comm]
  rw [he, Matrix.charpoly_diagonal]
  rw [← (chebyshev1.SineJacobi.nodeIndex N hN).prod_comp]
  simp only [J.eigenvalue_nodeIndex hN ht, normalizedGreenValue_eq]

/--
The normalized eigenvalues of Lemma 1 are in strictly decreasing order.

The precise assertion is `StrictAnti (normalizedGreenValue N)`.

Use: `chebyshev2.Continuum.green_eigenvalue_eq` uses this assertion to establish exact
identity `(greenSpectralData J hN ht).eigenvalue = finiteEigenvalue N`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.nodeAngle_mem`,
`chebyshev2.Jacobi.normalizedGreenValue_eq` with the arguments shown in the proof.
-/
theorem normalizedGreenValue_strictAnti (N : ℕ) : StrictAnti (normalizedGreenValue N) := by
  -- Use the identities/estimates `chebyshev1.SineJacobi.nodeAngle_mem`,
  -- `chebyshev2.Jacobi.normalizedGreenValue_eq` with the arguments shown in the proof.
  intro i j hij
  have hN : 0 < N := by omega
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hi := chebyshev1.SineJacobi.nodeAngle_mem N i
  have hj := chebyshev1.SineJacobi.nodeAngle_mem N j
  have hang : chebyshev1.SineJacobi.nodeAngle N i < chebyshev1.SineJacobi.nodeAngle N j := by
    unfold chebyshev1.SineJacobi.nodeAngle
    apply div_lt_div_of_pos_right ?_ (by positivity)
    apply mul_lt_mul_of_pos_right ?_ pi_pos
    have h : (i:ℝ) < (j:ℝ) := by exact_mod_cast hij
    linarith
  have hcos := cos_lt_cos_of_nonneg_of_le_pi hi.1.le hj.2.le hang
  have h1 : chebyshev1.SineJacobi.node N i < 1 := by
    have hh := cos_lt_cos_of_nonneg_of_le_pi (by norm_num) hi.2.le hi.1
    simpa [chebyshev1.SineJacobi.node] using hh
  rw [normalizedGreenValue_eq, normalizedGreenValue_eq]
  apply div_lt_div_of_pos_right ?_ (pow_pos hn 2)
  rw [← one_div (1-chebyshev1.SineJacobi.node N j), ← one_div (1-chebyshev1.SineJacobi.node N i)]
  apply one_div_lt_one_div_of_lt (sub_pos.mpr h1)
  change 1-chebyshev1.SineJacobi.node N i < 1-chebyshev1.SineJacobi.node N j
  dsimp [chebyshev1.SineJacobi.node]
  linarith

end
end chebyshev2.Jacobi
