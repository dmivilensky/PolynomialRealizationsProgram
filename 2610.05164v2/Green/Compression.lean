import «2610.05164v2».Green.LiftIdentities
import «2610.05164v2».Finite.Horizon

/-!
Article: 2610.05164v2, Theorem A.1.
Compression.
Use: `«2610.05164v2».Centering.compression_matrix` feeds
`«2610.05164v2».Centering.charpoly_compression` (charpoly compression).
Proof chain: `«2610.05164v2».centeringEquiv` — 2610.05164v2, Theorem A.1; Centering lift,
contractivity, odd Green entries and characteristic polynomial.
-/
namespace «2610.05164v2».Centering
noncomputable section
open «2606.16671v2» Matrix Real
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} (C : Jacobi (2*N))

/--
Defines `diagonal` of type `ℝ` by `sqrt (C.data.aSq (2*i.val+1))`.

Use: `«2610.05164v2».Centering.compression_matrix` rewrites with this definition to establish
exact identity `(compression C).matrix = (2:ℝ) • (extractedBlock C*(extractedBlock C)ᵀ)-1`.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».centeringEquiv`.
-/
def diagonal (i : Fin N) : ℝ := sqrt (C.data.aSq (2*i.val+1))
/--
Defines `lower` of type `ℝ` by `sqrt (C.data.aSq (2*i.val))`.

Use: `«2610.05164v2».Centering.compression_matrix` rewrites with this definition to establish
exact identity `(compression C).matrix = (2:ℝ) • (extractedBlock C*(extractedBlock C)ᵀ)-1`.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».centeringEquiv`.
-/
def lower (i : Fin N) : ℝ := sqrt (C.data.aSq (2*i.val))
/--
Defines `extractedBlock` of type `` by `Bidiagonal.matrix (diagonal C) (lower C)`.

Use: `«2610.05164v2».Centering.compression_matrix` rewrites with this definition to establish
exact identity `(compression C).matrix = (2:ℝ) • (extractedBlock C*(extractedBlock C)ᵀ)-1`.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».centeringEquiv`.
-/
def extractedBlock := Bidiagonal.matrix (diagonal C) (lower C)

/--
The stated quantitative bound `0 < diagonal C i`.

Use: `«2610.05164v2».Centering.extractedBlock_is_cholesky` uses this bound to establish exact
identity `extractedBlock C = (compression C).cholesky`.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».centeringEquiv`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem diagonal_pos (hc : C.Centered) (i : Fin N) : 0 < diagonal C i :=
  sqrt_pos.mpr (hc.1 _ (by omega) (by omega))
/--
Exact identity `lower C i = 0`.

Use: `«2610.05164v2».Centering.extractedBlock_is_cholesky` uses this identity to establish
exact identity `extractedBlock C = (compression C).cholesky`.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».centeringEquiv`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem lower_zero (i : Fin N) (hi : i.val = 0) : lower C i = 0 := by
  simp [lower,hi,C.coupling_zero]
/--
The stated quantitative bound `0 < lower C i`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem A.1.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem lower_pos (hc : C.Centered) (i : Fin N) (hi : 0 < i.val) : 0 < lower C i :=
  sqrt_pos.mpr (hc.1 _ (by omega) (by omega))

/--
Constructs `compressionData` of type `JacobiData` by the displayed record fields. Data fields
specify the construction; proof fields discharge its required properties.

Use: `«2610.05164v2».Centering.compression` uses this definition in the displayed construction
of `compression`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».centeringEquiv`.
-/
def compressionData : JacobiData where
  b n := if n < N then 2*(C.data.aSq (2*n+1)+C.data.aSq (2*n))-1 else 0
  aSq n := if 0 < n ∧ n < N then 4*C.data.aSq (2*n)*C.data.aSq (2*n-1) else 0

/--
Constructs `compression` of type `Jacobi N` by the displayed record fields. Data fields specify
the construction; proof fields discharge its required properties.

Use: `«2610.05164v2».Centering.compression_irreducible` rewrites with this definition to
establish the precise assertion is `(compression C).Irreducible`.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».centeringEquiv`.
-/
def compression : Jacobi N where
  data := compressionData C
  coupling_nonneg n := by
    dsimp [compressionData]
    split_ifs
    · exact mul_nonneg (mul_nonneg (by norm_num) (C.coupling_nonneg _)) (C.coupling_nonneg _)
    · exact le_rfl
  coupling_zero := by simp [compressionData]
  diagonal_tail n hn := by simp [compressionData,not_lt.mpr hn]
  coupling_tail n hn := by simp [compressionData,not_lt.mpr hn]

/--
The precise assertion is `(compression C).Irreducible`.

Use: `«2610.05164v2».centeringEquiv` uses this assertion in the displayed construction of
`centeringEquiv`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».centeringEquiv`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem compression_irreducible (hc : C.Centered) : (compression C).Irreducible := by
  intro n hn hnN
  simp only [compression, compressionData, hn, hnN, and_self, ite_true]
  exact mul_pos (mul_pos (by norm_num) (hc.1 _ (by omega) (by omega)))
    (hc.1 _ (by omega) (by omega))

/--
Exact identity `(compression C).matrix = (2:ℝ) • (extractedBlock C*(extractedBlock C)ᵀ)-1`.

Use: `«2610.05164v2».Centering.charpoly_compression` rewrites with this identity to establish
exact identity `C.matrix.charpoly = Polynomial.C ((1/2:ℝ)^N)*(compression
C).matrix.charpoly.comp (2*Polynomial.X^2-1)`.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».centeringEquiv`.

Proof: Separate `i = j` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem compression_matrix : (compression C).matrix =
    (2:ℝ) • (extractedBlock C*(extractedBlock C)ᵀ)-1 := by
  -- Separate `i = j` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  ext i j
  simp only [Jacobi.matrix, compression, compressionData, JacobiData.matrix_apply,
    Nat.zero_add, extractedBlock, Bidiagonal.mul_transpose_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  by_cases hij : i = j
  · subst j
    simp only [ite_true, i.isLt]
    rw [diagonal, lower, sq_sqrt (C.coupling_nonneg _), sq_sqrt (C.coupling_nonneg _)]
    by_cases hi : 0 < i.val
    · simp [hi]
    · have hi0 : i.val = 0 := by omega
      simp [hi0,C.coupling_zero]
  · simp only [hij,ite_false]
    by_cases ha : i.val+1 = j.val
    · have hj : 0 < j.val := by omega
      have hprev : 2*j.val-1 = 2*i.val+1 := by omega
      simp only [ha,ite_true,hj,j.isLt,and_self]
      rw [diagonal, lower, sqrt_mul (mul_nonneg (by norm_num) (C.coupling_nonneg _)),
        sqrt_mul (by norm_num : (0:ℝ) ≤ 4), hprev]
      norm_num; ring
    · simp only [ha,ite_false]
      by_cases hb : j.val+1 = i.val
      · have hi : 0 < i.val := by omega
        have hprev : 2*i.val-1 = 2*j.val+1 := by omega
        simp only [hb,ite_true,hi,i.isLt,and_self]
        rw [diagonal, lower, sqrt_mul (mul_nonneg (by norm_num) (C.coupling_nonneg _)),
          sqrt_mul (by norm_num : (0:ℝ) ≤ 4), hprev]
        norm_num; ring
      · simp [hb]

end
end «2610.05164v2».Centering
