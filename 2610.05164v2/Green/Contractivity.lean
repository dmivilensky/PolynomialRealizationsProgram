import «2610.05164v2».Green.SpectralCoordinates
import «2606.16671v2».Realization.StaticShiftGeneral
import Mathlib.Analysis.Matrix.Order

/-!
Article: 2610.05164v2, Theorem A.1.
Contractivity.
Use: `«2610.05164v2».Jacobi.contractive_of_pencils` feeds
`«2610.05164v2».Packing.Jacobi.coupling_cost_bound` (The explicit coupling has the article's cost
1/(2N)).
Proof chain: `«2610.05164v2».Jacobi.lift_contractive` — 2610.05164v2, Theorem A.1; Centering lift,
contractivity, odd Green entries and characteristic polynomial.
-/
namespace «2610.05164v2».Jacobi
noncomputable section
open «2606.16671v2» Matrix
open scoped Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} (J : Jacobi N)

/--
The precise assertion is `(1-J.matrix).PosDef ∧ (1+J.matrix).PosDef`.

Use: `«2610.05164v2».Jacobi.contractive_iff_pencils` uses this assertion to establish
equivalence of the displayed criteria: `«2606.16671v2».opNorm J.matrix < 1 ↔
(1-J.matrix).PosDef ∧ (1+J.matrix).PosDef`.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».Jacobi.lift_contractive`.

Proof: Use the identities/estimates `«2606.16671v2».eval_abs_le_opNorm`,
`«2610.05164v2».Jacobi.matrix_isHermitian`, `«2610.05164v2».Jacobi.affine_posDef` with the
arguments shown in the proof.
-/
theorem pencils_of_contractive (h : «2606.16671v2».opNorm J.matrix < 1) :
    (1-J.matrix).PosDef ∧ (1+J.matrix).PosDef := by
  -- Use the identities/estimates `«2606.16671v2».eval_abs_le_opNorm`,
  -- `«2610.05164v2».Jacobi.matrix_isHermitian`, `«2610.05164v2».Jacobi.affine_posDef` with the
  -- arguments shown in the proof.
  have hx (x : ℝ) (hx : x ∈ spectrum ℝ J.matrix) : |x| < 1 := by
    have he := «2606.16671v2».eval_abs_le_opNorm Polynomial.X J.matrix J.matrix_isHermitian x hx
    simp only [Polynomial.aeval_X, Polynomial.eval_X] at he
    exact he.trans_lt h
  constructor
  · have hp := J.affine_posDef 1 (-1) (fun x hs => by
      have hh := (abs_lt.mp (hx x hs)).2; linarith)
    simpa [Matrix.scalar, sub_eq_add_neg] using hp
  · have hp := J.affine_posDef 1 1 (fun x hs => by
      have hh := (abs_lt.mp (hx x hs)).1; linarith)
    simpa [Matrix.scalar] using hp

/--
The stated quantitative bound `«2606.16671v2».opNorm J.matrix < 1`.

Use: `«2610.05164v2».Jacobi.contractive_iff_pencils` uses this bound to establish equivalence
of the displayed criteria: `«2606.16671v2».opNorm J.matrix < 1 ↔ (1-J.matrix).PosDef ∧
(1+J.matrix).PosDef`.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».Jacobi.lift_contractive`.

Proof: Use the identities/estimates `«2610.05164v2».Jacobi.matrix_isHermitian`,
`«2606.16671v2».opNorm_aeval_eq`, `«2610.05164v2».SpectralCoordinates.coordinates_one` with the
arguments shown in the proof.
-/
theorem contractive_of_pencils (hm : (1-J.matrix).PosDef) (hp : (1+J.matrix).PosDef) :
    «2606.16671v2».opNorm J.matrix < 1 := by
  -- Use the identities/estimates `«2610.05164v2».Jacobi.matrix_isHermitian`,
  -- `«2606.16671v2».opNorm_aeval_eq`, `«2610.05164v2».SpectralCoordinates.coordinates_one`
  -- with the arguments shown in the proof.
  let B := «2606.16671v2».SpectralBasis.ofHermitian J.matrix J.matrix_isHermitian
  have hq : Function.Injective B.Q.mulVec := by
    intro x y he
    have hh := congrArg (fun v => B.Qᵀ*ᵥv) he
    simpa [Matrix.mulVec_mulVec, B.transpose_mul] using hh
  have hc (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.PosDef) : (B.coordinates A).PosDef := by
    simpa only [SpectralBasis.coordinates, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hA.conjTranspose_mul_mul_same hq
  have hm' := hc _ hm
  have hp' := hc _ hp
  have hb : B.coordinates J.matrix = Matrix.diagonal B.eigenvalues := B.diagonalize
  rw [SpectralCoordinates.coordinates_sub, SpectralCoordinates.coordinates_one, hb,
    ← Matrix.diagonal_one, Matrix.diagonal_sub, Matrix.posDef_diagonal_iff] at hm'
  have he : B.coordinates (1+J.matrix) = Matrix.diagonal (fun i => 1+B.eigenvalues i) := by
    simp only [SpectralBasis.coordinates, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      B.transpose_mul, B.diagonalize]
    rw [← Matrix.diagonal_one, Matrix.diagonal_add]
  rw [he, Matrix.posDef_diagonal_iff] at hp'
  have hn := «2606.16671v2».opNorm_aeval_eq Polynomial.X J.matrix J.matrix_isHermitian
  simp only [Polynomial.aeval_X, Polynomial.eval_X] at hn
  rw [hn, pi_norm_lt_iff (by norm_num : (0:ℝ) < 1)]
  intro i
  change ‖B.eigenvalues i‖ < 1
  rw [Real.norm_eq_abs, abs_lt]
  constructor <;> linarith [hm' i, hp' i]

/--
Equivalence of the displayed criteria: `«2606.16671v2».opNorm J.matrix < 1 ↔
(1-J.matrix).PosDef ∧ (1+J.matrix).PosDef`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem A.1.

Proof: Use the identities/estimates `«2610.05164v2».Jacobi.pencils_of_contractive`,
`«2610.05164v2».Jacobi.contractive_of_pencils` with the arguments shown in the proof.
-/
theorem contractive_iff_pencils : «2606.16671v2».opNorm J.matrix < 1 ↔
    (1-J.matrix).PosDef ∧ (1+J.matrix).PosDef :=
  ⟨J.pencils_of_contractive, fun h => J.contractive_of_pencils h.1 h.2⟩

end
end «2610.05164v2».Jacobi
