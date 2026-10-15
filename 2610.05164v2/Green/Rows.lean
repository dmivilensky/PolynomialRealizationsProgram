import «2610.05164v2».Green.Bidiagonal
import «2610.05164v2».Green.Positivity

/-!
Article: 2610.05164v2, Proposition 1.
Rows.
Use: `«2610.05164v2».Jacobi.green_row` feeds `«2610.05164v2».Jacobi.green_neighbor_minor` (The
adjacent Green minor identity, derived from the inverse equations).
Proof chain: `«2610.05164v2».Packing.exists_representation` — 2610.05164v2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
-/
namespace «2610.05164v2».Jacobi
noncomputable section
open «2606.16671v2» Matrix
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} (J : Jacobi N)

/--
Exact identity `(∑ k : Fin N, (1-J.matrix) i k*f k) = (1-J.data.b i.val)*f i - (if h : 0 <
i.val then Real.sqrt (J.data.aSq i.val)*f ⟨i.val-1,by omega⟩ else 0) - (if h : i.val+1 < N then
Real.sqrt (J.data.aSq (i.val+1))*f ⟨i.val+1,h⟩ else 0)`.

Use: `«2610.05164v2».Jacobi.green_row` rewrites with this identity to establish the identity
stated in that declaration.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.exists_representation`.

Proof: Separate `i = k` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem pencil_row (i : Fin N) (f : Fin N → ℝ) :
    (∑ k : Fin N, (1-J.matrix) i k*f k) = (1-J.data.b i.val)*f i -
      (if h : 0 < i.val then Real.sqrt (J.data.aSq i.val)*f ⟨i.val-1,by omega⟩ else 0) -
      (if h : i.val+1 < N then Real.sqrt (J.data.aSq (i.val+1))*f ⟨i.val+1,h⟩ else 0) := by
  -- Separate `i = k` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  have ha (k : Fin N) : (1-J.matrix) i k =
      (if i = k then 1-J.data.b i.val else 0) +
      (if k.val+1 = i.val then -Real.sqrt (J.data.aSq i.val) else 0) +
      (if i.val+1 = k.val then -Real.sqrt (J.data.aSq k.val) else 0) := by
    simp only [Matrix.sub_apply, matrix, J.data.matrix_apply, Nat.zero_add, Matrix.one_apply]
    by_cases hik : i = k
    · subst k; simp
    · simp only [hik, ite_false, zero_sub]
      have hv : i.val ≠ k.val := fun he => hik (Fin.ext he)
      by_cases hu : i.val+1 = k.val
      · have hl : ¬k.val+1 = i.val := by omega
        simp [hu, hl]
      · by_cases hl : k.val+1 = i.val <;> simp [hu,hl]
  simp only [ha, add_mul, Finset.sum_add_distrib]
  have he := Bidiagonal.row_mul (fun k => 1-J.data.b k.val)
    (fun k => -Real.sqrt (J.data.aSq k.val)) i f
  simp only [Bidiagonal.matrix, add_mul, Finset.sum_add_distrib] at he
  rw [he]
  have hu : (∑ k : Fin N, (if i.val+1 = k.val then -Real.sqrt (J.data.aSq k.val) else 0)*f k) =
      if h : i.val+1 < N then -Real.sqrt (J.data.aSq (i.val+1))*f ⟨i.val+1,h⟩ else 0 := by
    by_cases hi : i.val+1 < N
    · let p : Fin N := ⟨i.val+1,hi⟩
      have he (k : Fin N) : i.val+1 = k.val ↔ k = p := by
        rw [Fin.ext_iff]; dsimp [p]; omega
      simp [hi, he, ite_mul, p]
    · have he (k : Fin N) : ¬i.val+1 = k.val := by omega
      simp [hi, he]
  rw [hu]
  split_ifs <;> ring

/--
Exact identity `(1-J.data.b i.val)*J.green i j - (if h : 0 < i.val then Real.sqrt (J.data.aSq
i.val)*J.green ⟨i.val-1,by omega⟩ j else 0) - (if h : i.val+1 < N then Real.sqrt (J.data.aSq
(i.val+1))*J.green ⟨i.val+1,h⟩ j else 0) = if i = j then 1 else 0`.

Use: `«2610.05164v2».Jacobi.centered_green_diagonal` uses this identity to establish exact
identity `J.green i i = 1+J.incomingFlow i+J.edgeFlow i`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.exists_representation`.

Proof: Use the identities/estimates `«2610.05164v2».Jacobi.pencil_row` with the arguments shown
in the proof.
-/
theorem green_row (hm : (1-J.matrix).PosDef) (i j : Fin N) :
    (1-J.data.b i.val)*J.green i j -
      (if h : 0 < i.val then Real.sqrt (J.data.aSq i.val)*J.green ⟨i.val-1,by omega⟩ j else 0) -
      (if h : i.val+1 < N then Real.sqrt (J.data.aSq (i.val+1))*J.green ⟨i.val+1,h⟩ j else 0) =
      if i = j then 1 else 0 := by
  -- Use the identities/estimates `«2610.05164v2».Jacobi.pencil_row` with the arguments shown
  -- in the proof.
  have he := congrArg (fun A => A i j)
    (Matrix.mul_nonsing_inv (1-J.matrix) (isUnit_iff_ne_zero.mpr hm.det_pos.ne'))
  rw [Matrix.mul_apply, J.pencil_row] at he
  exact he

end
end «2610.05164v2».Jacobi
