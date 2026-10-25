import chebyshev2.Finite.Basic

/-!
Article: chebyshev2, Proposition 1.
Positive diagonal entries make the lower bidiagonal factor unique.
Use: `chebyshev2.Bidiagonal.factor_unique` feeds `chebyshev2.Jacobi.cholesky_unique`
(Uniqueness of the factor, including its finite coefficient representation).
Proof chain: `chebyshev2.Jacobi.cholesky_unique` — chebyshev2, Theorem A.1; Centering lift,
contractivity, odd Green entries and characteristic polynomial.
-/
namespace chebyshev2.Bidiagonal
noncomputable section
open scoped BigOperators Matrix
variable {N : ℕ}

/--
A lower bidiagonal matrix; the subdiagonal is indexed by its destination row.

Use: `chebyshev2.Bidiagonal.mul_transpose_apply` rewrites with this definition to establish
exact identity `(matrix d l * (matrix d l)ᵀ) i j = if i = j then d i^2 + (if 0 < i.val then l
i^2 else 0) else if i.val+1 = j.val then d i*l j else if j.val+1 = i.val then l i*d j else 0`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.cholesky_factor`.
-/
def matrix (d l : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ := fun i j =>
  (if i = j then d i else 0) + (if j.val+1 = i.val then l i else 0)

/--
Exact identity `(∑ k : Fin N, matrix d l i k * f k) = d i*f i + if h : 0 < i.val then l i*f
⟨i.val-1,by omega⟩ else 0`.

Use: `chebyshev2.Bidiagonal.mul_transpose_apply` rewrites with this identity to establish
exact identity `(matrix d l * (matrix d l)ᵀ) i j = if i = j then d i^2 + (if 0 < i.val then l
i^2 else 0) else if i.val+1 = j.val then d i*l j else if j.val+1 = i.val then l i*d j else 0`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.cholesky_factor`.

Proof: Separate `0 < i.val` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem row_mul (d l : Fin N → ℝ) (i : Fin N) (f : Fin N → ℝ) :
    (∑ k : Fin N, matrix d l i k * f k) = d i*f i +
      if h : 0 < i.val then l i*f ⟨i.val-1,by omega⟩ else 0 := by
  -- Separate `0 < i.val` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  simp only [matrix, add_mul, Finset.sum_add_distrib]
  have hd : (∑ k : Fin N, (if i = k then d i else 0)*f k) = d i*f i := by
    simp [ite_mul]
  rw [hd]
  congr 1
  by_cases hi : 0 < i.val
  · simp only [hi, dite_true]
    let p : Fin N := ⟨i.val-1,by omega⟩
    have he (k : Fin N) : k.val+1 = i.val ↔ k = p := by
      rw [Fin.ext_iff]
      change k.val+1 = i.val ↔ k.val = i.val-1
      omega
    simp only [he, ite_mul, zero_mul]
    simp [p]
  · have he (k : Fin N) : ¬k.val+1 = i.val := by omega
    simp [hi, he]

/--
Exact identity `(matrix d l * (matrix d l)ᵀ) i j = if i = j then d i^2 + (if 0 < i.val then l
i^2 else 0) else if i.val+1 = j.val then d i*l j else if j.val+1 = i.val then l i*d j else 0`.

Use: `chebyshev2.Bidiagonal.factor_unique` rewrites with this identity to establish exact
identity `d = d' ∧ l = l'`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.cholesky_factor`.

Proof: Separate `0 < i.val` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem mul_transpose_apply (d l : Fin N → ℝ) (i j : Fin N) :
    (matrix d l * (matrix d l)ᵀ) i j =
      if i = j then d i^2 + (if 0 < i.val then l i^2 else 0)
      else if i.val+1 = j.val then d i*l j
      else if j.val+1 = i.val then l i*d j else 0 := by
  -- Separate `0 < i.val` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  rw [row_mul]
  by_cases hi : 0 < i.val
  · simp only [hi, dite_true]
    have hp : i.val-1+1 = i.val := by omega
    have he : j = (⟨i.val-1,by omega⟩ : Fin N) ↔ j.val+1 = i.val := by
      rw [Fin.ext_iff]
      change j.val = i.val-1 ↔ j.val+1 = i.val
      omega
    simp only [matrix, hp, he]
    by_cases hij : i = j
    · subst j
      simp [pow_two]
    · have hji : j ≠ i := Ne.symm hij
      have hv : i.val ≠ j.val := fun he => hij (Fin.ext he)
      by_cases ha : i.val+1 = j.val
      · have hb : ¬j.val+1 = i.val := by omega
        simp [hij,hji,hv,ha,hb]
      · by_cases hb : j.val+1 = i.val
        · simp [hij,hji,hv,ha,hb]
        · simp [hij,hji,hv,ha,hb]
  · simp only [hi, dite_false]
    have hb : ¬j.val+1 = i.val := by omega
    simp only [matrix]
    by_cases hij : i = j
    · subst j; simp [pow_two]
    · by_cases ha : i.val+1 = j.val
      · simp [hij, Ne.symm hij, ha]
      · simp [hij, Ne.symm hij, ha, hb]

/--
Positive diagonal entries make the lower bidiagonal factor unique. The unused zeroth
subdiagonal coefficient is fixed to zero.

Exact identity `d = d' ∧ l = l'`.

Use: `chebyshev2.Jacobi.cholesky_unique` uses this identity to establish the identity `d
= J.choleskyDiagonal ∧ l = J.choleskyLower`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.cholesky_unique`.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion. Prove equality of
functions by evaluating both sides at an arbitrary argument.
-/
theorem factor_unique (d l d' l' : Fin N → ℝ)
    (hd : ∀ i, 0 < d i) (hd' : ∀ i, 0 < d' i)
    (hl : ∀ i, i.val = 0 → l i = 0) (hl' : ∀ i, i.val = 0 → l' i = 0)
    (h : matrix d l * (matrix d l)ᵀ = matrix d' l' * (matrix d' l')ᵀ) :
    d = d' ∧ l = l' := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  have hi : ∀ n, ∀ i : Fin N, i.val = n → d i = d' i ∧ l i = l' i := by
    intro n
    induction n with
    | zero =>
      intro i hi
      have he := congrArg (fun A => A i i) h
      simp only [mul_transpose_apply, ite_true, hi, Nat.lt_irrefl, ite_false,
        add_zero] at he
      exact ⟨by nlinarith [hd i, hd' i], by rw [hl i hi, hl' i hi]⟩
    | succ n ih =>
      intro i hi
      let p : Fin N := ⟨n, by omega⟩
      obtain ⟨hp, _⟩ := ih p rfl
      have hip : i ≠ p := by intro he; have := congrArg Fin.val he; simp [p, hi] at this
      have hpi : p.val+1 = i.val := by simp [p, hi]
      have hin : ¬i.val+1 = p.val := by dsimp [p]; omega
      have he := congrArg (fun A => A i p) h
      simp only [mul_transpose_apply, hip, ite_false, hin, hpi, ite_true, hp] at he
      have hli : l i = l' i := (mul_right_cancel₀ (hd' p).ne') he
      have he := congrArg (fun A => A i i) h
      have hi0 : 0 < i.val := by omega
      simp only [mul_transpose_apply, ite_true, hi0, hli] at he
      exact ⟨by nlinarith [hd i, hd' i], hli⟩
  exact ⟨funext fun i => (hi i.val i rfl).1, funext fun i => (hi i.val i rfl).2⟩

end
end chebyshev2.Bidiagonal
