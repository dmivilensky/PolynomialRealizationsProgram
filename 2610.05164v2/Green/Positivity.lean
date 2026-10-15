import «2610.05164v2».Finite.Basic

/-!
Article: 2610.05164v2, Corollary 1.
The positive affine pencils used at both ends of the Jacobi spectrum.
Use: `«2610.05164v2».Jacobi.energy_pos` feeds `«2610.05164v2».Jacobi.symmetric_gain_bounds`
(Corollary 1: the lower bound is already attained by scalar symmetric perturbations).
Proof chain: `«2610.05164v2».Jacobi.gain_attained_dim_two` — 2610.05164v2, Theorem 2.2; Sharp gain
formula, derivative and attaining examples.
-/
namespace «2610.05164v2».Jacobi
noncomputable section
open «2606.16671v2» Polynomial Polynomial.Chebyshev Matrix Unitary
open scoped Matrix ComplexOrder
variable {N : ℕ} (J : Jacobi N)

/--
The precise assertion is `spectrum ℝ J.matrix ⊆ Set.Ioo (-1) 1`.

Use: `«2610.05164v2».Jacobi.one_add_posDef` uses this assertion to establish the precise
assertion is `(1+J.matrix).PosDef`.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».Jacobi.green_trace_square`.

Proof: Use the identities/estimates `«2610.05164v2».Jacobi.spectrum_subset`,
`«2610.05164v2».fiberPolynomial_eq`, `«2610.05164v2».Jacobi.charpoly_eq` with the arguments
shown in the proof.
-/
theorem spectrum_subset_open (hN : 0 < N) (h : J.Terminal) :
    spectrum ℝ J.matrix ⊆ Set.Ioo (-1) 1 := by
  -- Use the identities/estimates `«2610.05164v2».Jacobi.spectrum_subset`,
  -- `«2610.05164v2».fiberPolynomial_eq`, `«2610.05164v2».Jacobi.charpoly_eq` with the
  -- arguments shown in the proof.
  intro x hx
  have hb := J.spectrum_subset hN h hx
  have hp := Matrix.mem_spectrum_iff_isRoot_charpoly.mp hx
  rw [J.charpoly_eq h, fiberPolynomial_eq N hN] at hp
  have h1 : x ≠ 1 := by
    intro he; subst x
    simp [IsRoot] at hp
  have hm : x ≠ -1 := by
    intro he; subst x
    simp [IsRoot] at hp
  exact ⟨lt_of_le_of_ne hb.1 hm.symm, lt_of_le_of_ne hb.2 h1⟩

/--
The positive affine pencils used at both ends of the Jacobi spectrum.

The precise assertion is `(Matrix.scalar (Fin N) a + b • J.matrix).PosDef`.

Use: `«2610.05164v2».Jacobi.one_add_posDef` uses this assertion to establish the precise
assertion is `(1+J.matrix).PosDef`.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».Jacobi.lift_contractive`.

Proof: Use the identities/estimates `«2610.05164v2».Jacobi.matrix_isHermitian`,
`«2606.16671v2».aeval_diagonal` with the arguments shown in the proof.
-/
theorem affine_posDef (a b : ℝ)
    (h : ∀ x ∈ spectrum ℝ J.matrix, 0 < a+b*x) :
    (Matrix.scalar (Fin N) a + b • J.matrix).PosDef := by
  -- Use the identities/estimates `«2610.05164v2».Jacobi.matrix_isHermitian`,
  -- `«2606.16671v2».aeval_diagonal` with the arguments shown in the proof.
  have hM := J.matrix_isHermitian
  have hp : (aeval J.matrix (C a+C b*X)).PosDef := by
    rw [hM.spectral_theorem, Polynomial.aeval_algHom_apply]
    simp only [Unitary.conjStarAlgAut_apply, Function.comp_def, aeval_diagonal,
      RCLike.ofReal_real_eq_id, id_eq, eval_add, eval_mul, eval_C, eval_X]
    apply isUnit_coe.posDef_star_right_conjugate_iff.mpr
    apply Matrix.posDef_diagonal_iff.mpr
    intro i
    exact h _ (hM.eigenvalues_mem_spectrum_real i)
  simpa [map_add, map_mul, Polynomial.aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, Matrix.scalar] using hp

/--
The precise assertion is `(1-J.matrix).PosDef`.

Use: `«2610.05164v2».Jacobi.green_posDef` uses this assertion to establish the precise
assertion is `J.green.PosDef`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Proof: Use the identities/estimates `«2610.05164v2».Jacobi.affine_posDef`,
`«2610.05164v2».Jacobi.spectrum_subset_open` with the arguments shown in the proof.
-/
theorem one_sub_posDef (hN : 0 < N) (h : J.Terminal) : (1-J.matrix).PosDef := by
  have hp := J.affine_posDef 1 (-1) (fun x hx => by
    have hh := (J.spectrum_subset_open hN h hx).2; linarith)
  simpa [Matrix.scalar, sub_eq_add_neg] using hp

/--
The precise assertion is `(1+J.matrix).PosDef`.

Use: `«2610.05164v2».Centering.extractedBlock_is_cholesky` uses this assertion to establish
exact identity `extractedBlock C = (compression C).cholesky`.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».centeringEquiv`.

Proof: Use the identities/estimates `«2610.05164v2».Jacobi.affine_posDef`,
`«2610.05164v2».Jacobi.spectrum_subset_open` with the arguments shown in the proof.
-/
theorem one_add_posDef (hN : 0 < N) (h : J.Terminal) : (1+J.matrix).PosDef := by
  have hp := J.affine_posDef 1 1 (fun x hx => by
    have hh := (J.spectrum_subset_open hN h hx).1; linarith)
  simpa [Matrix.scalar] using hp

/--
The precise assertion is `J.green.PosDef`.

Use: `«2610.05164v2».Jacobi.green_diagonal_pos` uses this assertion to establish the stated
quantitative bound `0 < J.green i i`.

Article: 2610.05164v2, Corollary 1 via `«2610.05164v2».Jacobi.symmetric_gain_bounds`.

Proof: Use the identities/estimates `«2610.05164v2».Jacobi.one_sub_posDef` with the arguments
shown in the proof.
-/
theorem green_posDef (hN : 0 < N) (h : J.Terminal) : J.green.PosDef :=
  (J.one_sub_posDef hN h).inv

/--
The stated quantitative bound `0 < J.green i i`.

Use: `«2610.05164v2».Jacobi.energy_pos` uses this bound to establish the stated quantitative
bound `0 < J.energy`.

Article: 2610.05164v2, Corollary 1 via `«2610.05164v2».Jacobi.symmetric_gain_bounds`.

Proof: Use the identities/estimates `«2610.05164v2».Jacobi.green_posDef` with the arguments
shown in the proof.
-/
theorem green_diagonal_pos (hN : 0 < N) (h : J.Terminal) (i : Fin N) :
    0 < J.green i i := (J.green_posDef hN h).diag_pos

/--
The stated quantitative bound `0 < J.energy`.

Use: `«2610.05164v2».Jacobi.gain_pos` uses this bound to establish the stated quantitative
bound `0 < J.gain I (J.admissible I hN ht)`.

Article: 2610.05164v2, Corollary 1 via `«2610.05164v2».Jacobi.symmetric_gain_bounds`.

Proof: Use the identities/estimates `«2610.05164v2».Jacobi.green_diagonal_pos` with the
arguments shown in the proof.
-/
theorem energy_pos (hN : 0 < N) (h : J.Terminal) : 0 < J.energy := by
  apply Finset.sum_pos' (fun i _ => sq_nonneg _)
  exact ⟨⟨0,hN⟩, Finset.mem_univ _, sq_pos_of_pos (J.green_diagonal_pos hN h _)⟩

end
end «2610.05164v2».Jacobi
