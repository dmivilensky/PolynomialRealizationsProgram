import «2610.05164v2».Green.BlockLift
import «2610.05164v2».Green.LiftIndex

/-!
Article: 2610.05164v2, Theorem A.1.
The interlaced tridiagonal matrix is the odd/even block lift.
Use: `«2610.05164v2».Jacobi.lift_centered` feeds `«2610.05164v2».Jacobi.lift_interval_room` (The
space between neighboring even sites accommodates length 1/d_i).
-/
namespace «2610.05164v2».Jacobi
noncomputable section
open «2606.16671v2» Polynomial Matrix
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} (J : Jacobi N)

/--
Interlacing the diagonal and subdiagonal of the Cholesky factor.

Use: `«2610.05164v2».Jacobi.lift` uses this definition in the displayed construction of `lift`.
Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».Jacobi.lift_grouped_matrix`.
-/
def liftData : JacobiData where
  b _ := 0
  aSq n := if hn : n < 2*N then
    if n%2 = 1 then (J.choleskyDiagonal ⟨n/2,by omega⟩)^2
    else if 0 < n then (J.choleskyLower ⟨n/2,by omega⟩)^2 else 0
    else 0

/--
Constructs `lift` of type `Jacobi (2*N)` by the displayed record fields. Data fields specify
the construction; proof fields discharge its required properties.

Use: `«2610.05164v2».Jacobi.lift_even_coupling` rewrites with this definition to establish
exact identity `J.lift.data.aSq (2*i.val) = if 0 < i.val then J.choleskyLower i^2 else 0`.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».Jacobi.lift_grouped_matrix`.
-/
def lift : Jacobi (2*N) where
  data := J.liftData
  coupling_nonneg n := by dsimp [liftData]; split_ifs <;> positivity
  coupling_zero := by simp [liftData]
  diagonal_tail _ _ := rfl
  coupling_tail n hn := by simp [liftData, not_lt.mpr hn]

/--
Exact identity `J.lift.data.aSq (2*i.val+1) = J.choleskyDiagonal i^2`.

Use: `«2610.05164v2».Jacobi.lift_centered` rewrites with this identity to establish the precise
assertion is `J.lift.Centered`.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».Jacobi.lift_grouped_matrix`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem lift_odd_coupling (i : Fin N) :
    J.lift.data.aSq (2*i.val+1) = J.choleskyDiagonal i^2 := by
  have hn : 2*i.val+1 < 2*N := by omega
  simp [lift, liftData, hn, show (2*i.val+1)%2 = 1 by omega,
    show (2*i.val+1)/2 = i.val by omega]

/--
Exact identity `J.lift.data.aSq (2*i.val) = if 0 < i.val then J.choleskyLower i^2 else 0`.

Use: `«2610.05164v2».Jacobi.lift_centered` rewrites with this identity to establish the precise
assertion is `J.lift.Centered`.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».Jacobi.lift_grouped_matrix`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem lift_even_coupling (i : Fin N) :
    J.lift.data.aSq (2*i.val) = if 0 < i.val then J.choleskyLower i^2 else 0 := by
  have hn : 2*i.val < 2*N := by omega
  simp [lift, liftData, hn, show (2*i.val)%2 = 0 by omega,
    show (2*i.val)/2 = i.val by omega]

/--
The interlaced tridiagonal matrix is the odd/even block lift.

Exact identity `J.lift.matrix.submatrix (Centering.interleave N) (Centering.interleave N) =
Centering.blockLift J.cholesky`.

Use: `«2610.05164v2».Centering.lift_compression` rewrites with this identity to establish exact
identity `(compression C).lift = C`.

Article: 2610.05164v2, Theorem A.1.

Proof: Separate `i = j` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem lift_grouped_matrix :
    J.lift.matrix.submatrix (Centering.interleave N) (Centering.interleave N) =
      Centering.blockLift J.cholesky := by
  -- Separate `i = j` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have ha : ¬2*i.val+1 = 2*j.val := by omega
      have hb : ¬2*j.val+1 = 2*i.val := by omega
      simp [Matrix.submatrix, matrix, JacobiData.matrix_apply, Centering.blockLift,
        Centering.interleave_left, ha, hb, lift, liftData]
    | inr j =>
      have he : Centering.interleave N (Sum.inl i) ≠ Centering.interleave N (Sum.inr j) :=
        (Centering.interleave N).injective.ne (by simp)
      simp only [Matrix.submatrix_apply, matrix, JacobiData.matrix_apply, Nat.zero_add,
        he, ite_false, Centering.interleave_left, Centering.interleave_right,
        Centering.blockLift, Matrix.fromBlocks_apply₁₂, cholesky, Bidiagonal.matrix]
      by_cases hij : i = j
      · subst j
        simp [J.lift_odd_coupling, Real.sqrt_sq, choleskyDiagonal]
      · have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
        by_cases hb : j.val+1 = i.val
        · have hc : 2*j.val+1+1 = 2*i.val := by omega
          have hi : 0 < i.val := by omega
          simp [hv, hc, hij, hb, J.lift_even_coupling, hi, Real.sqrt_sq, choleskyLower]
        · have hc : ¬2*j.val+1+1 = 2*i.val := by omega
          simp [hv, hc, hij, hb]
  | inr i =>
    cases j with
    | inl j =>
      have he : Centering.interleave N (Sum.inr i) ≠ Centering.interleave N (Sum.inl j) :=
        (Centering.interleave N).injective.ne (by simp)
      simp only [Matrix.submatrix_apply, matrix, JacobiData.matrix_apply, Nat.zero_add,
        he, ite_false, Centering.interleave_left, Centering.interleave_right,
        Centering.blockLift, Matrix.fromBlocks_apply₂₁, Matrix.transpose_apply,
        cholesky, Bidiagonal.matrix]
      by_cases hij : j = i
      · subst j
        have ha : ¬2*i.val+1+1 = 2*i.val := by omega
        simp [ha, J.lift_odd_coupling, Real.sqrt_sq, choleskyDiagonal]
      · have hv : j.val ≠ i.val := fun h => hij (Fin.ext h)
        by_cases hb : i.val+1 = j.val
        · have hc : 2*i.val+1+1 = 2*j.val := by omega
          have hj : 0 < j.val := by omega
          simp [hc, hij, hb, J.lift_even_coupling, hj, Real.sqrt_sq, choleskyLower]
        · have hc : ¬2*i.val+1+1 = 2*j.val := by omega
          simp [hv, hc, hij, hb]
    | inr j =>
      have ha : ¬2*i.val+1 = 2*j.val := by omega
      have hb : ¬2*j.val+1 = 2*i.val := by omega
      simp [Matrix.submatrix, matrix, JacobiData.matrix_apply, Centering.blockLift,
        Centering.interleave_right, ha, hb, lift, liftData]

/--
The precise assertion is `J.lift.Centered`.

Use: `«2610.05164v2».Jacobi.even_le_intervalLeft` uses this assertion to establish the stated
quantitative bound `J.lift.position (by omega) ⟨2*i.val-1,by omega⟩ ≤ J.intervalLeft hN i`.

Article: 2610.05164v2, Theorem A.1.

Proof: Separate `n%2 = 1` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem lift_centered (h : (1+J.matrix).PosDef) (hir : J.Irreducible) :
    J.lift.Centered := by
  -- Separate `n%2 = 1` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  refine ⟨?_, fun _ _ => rfl⟩
  intro n hn hnN
  have hi : n/2 < N := by omega
  let i : Fin N := ⟨n/2,hi⟩
  by_cases ho : n%2 = 1
  · have he : n = 2*i.val+1 := by dsimp [i]; omega
    rw [he, J.lift_odd_coupling]
    exact sq_pos_of_pos (J.choleskyDiagonal_pos h i)
  · have he : n = 2*i.val := by dsimp [i]; omega
    have hi0 : 0 < i.val := by dsimp [i]; omega
    rw [he, J.lift_even_coupling, ite_eq_left hi0]
    exact sq_pos_of_pos (J.choleskyLower_pos h hir i hi0)

end
end «2610.05164v2».Jacobi
