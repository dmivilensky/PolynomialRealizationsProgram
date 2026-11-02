import bezout.Synthesis.Chebyshev

/-!
Article: bezout, Equation (34) (`eq:hall-expansion`).
Use: the explicit Chebyshev tensor behind the Flat and Balanced constructions.
Proof: a finite convolution satisfies the second-kind recurrence. Multiplication
by the coordinate difference gives the first-kind divided difference, and
polynomial differentiation supplies its continuous diagonal value.
-/

namespace bezout
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators

/-- The first-kind Chebyshev tensor has a half weight at degree zero.
Use: the Hall expansion with a uniform finite sum. -/
def hallTerm (m : ℕ) (x : ℝ) : ℝ :=
  if m = 0 then 1 / 2 else (T ℝ m).eval x

/-- The finite Hall convolution at terminal degree n+1.
Use: the common explicit tensor for both constructive realizations. -/
def hallSum (n : ℕ) (x y : ℝ) : ℝ :=
  ∑ m ∈ Finset.range (n + 1), hallTerm m x * (U ℝ ((n - m : ℕ) : ℤ)).eval y

/-- The finite convolution obeys the second-kind recurrence with its last source.
Use: proves the Hall expansion using only finite algebra. -/
theorem hallSum_add_two (n : ℕ) (x y : ℝ) :
    hallSum (n + 2) x y = 2 * y * hallSum (n + 1) x y - hallSum n x y
      + (T ℝ ((n + 2 : ℕ) : ℤ)).eval x := by
  unfold hallSum
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ (fun m => hallTerm m x * (U ℝ ((n + 1 - m : ℕ) : ℤ)).eval y)]
  have hsum :
      (∑ m ∈ Finset.range (n + 1), hallTerm m x * (U ℝ ((n + 2 - m : ℕ) : ℤ)).eval y) =
        2 * y * (∑ m ∈ Finset.range (n + 1), hallTerm m x * (U ℝ ((n + 1 - m : ℕ) : ℤ)).eval y)
          - ∑ m ∈ Finset.range (n + 1), hallTerm m x * (U ℝ ((n - m : ℕ) : ℤ)).eval y := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    have hm' : m ≤ n := by have := Finset.mem_range.mp hm; omega
    have hr := congrArg (fun p : ℝ[X] => p.eval y) (U_add_two ℝ ((n - m : ℕ) : ℤ))
    have h1 : n + 1 - m = (n - m) + 1 := by omega
    have h2 : n + 2 - m = (n - m) + 2 := by omega
    simp only [h1, h2, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, eval_sub,
      eval_mul, eval_ofNat, eval_X] at hr ⊢
    rw [hr]
    ring
  rw [hsum]
  simp [hallTerm, show n + 2 - (n + 1) = 1 by omega]

  ring

/-- The Hall tensor multiplied by the coordinate difference is the Chebyshev difference.
Use: a denominator-free identity, including equal coordinates. -/
theorem hallSum_difference (n : ℕ) (x y : ℝ) :
    2 * (x - y) * hallSum n x y = (T ℝ ((n + 1 : ℕ) : ℤ)).eval x - (T ℝ ((n + 1 : ℕ) : ℤ)).eval y := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [hallSum, hallTerm]; ring
  | one => norm_num [hallSum, hallTerm, Finset.sum_range_succ, T_two, U_one]; ring
  | more n ih0 ih1 =>
    rw [hallSum_add_two]
    have hx := congrArg (fun p : ℝ[X] => p.eval x) (T_add_two ℝ ((n + 1 : ℕ) : ℤ))
    have hy := congrArg (fun p : ℝ[X] => p.eval y) (T_add_two ℝ ((n + 1 : ℕ) : ℤ))
    simp only [Nat.cast_add, Nat.cast_one, eval_sub, eval_mul,
      eval_ofNat, eval_X] at hx hy
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at ih0 ih1 ⊢
    have hi : (n : ℤ) + 1 + 1 = (n : ℤ) + 2 := by ring
    have hj : (n : ℤ) + 1 + 2 = (n : ℤ) + 2 + 1 := by ring
    rw [hi] at ih1
    rw [hi, hj] at hx hy
    linear_combination 2 * y * ih1 - ih0 - hx + hy

/-- A polynomial form of the Hall convolution in its first coordinate.
Use: identifies the continuous diagonal by polynomial differentiation. -/
def hallPolynomial (n : ℕ) (y : ℝ) : ℝ[X] :=
  ∑ m ∈ Finset.range (n + 1),
    C ((U ℝ ((n - m : ℕ) : ℤ)).eval y) * (if m = 0 then C (1 / 2) else T ℝ m)

/-- Evaluation of the tensor polynomial is the finite Hall convolution.
Use: transfers scalar algebra to polynomial differentiation. -/
@[simp] theorem hallPolynomial_eval (n : ℕ) (x y : ℝ) :
    (hallPolynomial n y).eval x = hallSum n x y := by
  simp only [hallPolynomial, hallSum, eval_finsetSum, eval_mul]
  apply Finset.sum_congr rfl
  intro m _
  split_ifs <;> simp_all [hallTerm, mul_comm]

/-- The Hall expansion is exactly the continuously extended Chebyshev Bezoutian.
Use: unconditional tensor identities for the Flat and Balanced constructions. -/
theorem hall_expansion (n : ℕ) (x y : ℝ) :
    chebyshevBezout (n + 1) x y = hallSum n x y := by
  by_cases hxy : x = y
  · subst y
    have hp : 2 * (X - C x) * hallPolynomial n x = T ℝ ((n + 1 : ℕ) : ℤ) - C ((T ℝ ((n + 1 : ℕ) : ℤ)).eval x) := by
      apply Polynomial.funext
      intro z
      simpa only [eval_mul, eval_ofNat, eval_sub, eval_X, eval_C, hallPolynomial_eval]
        using hallSum_difference n z x
    have hd := congrArg (fun p : ℝ[X] => p.derivative.eval x) hp
    simp only [derivative_mul, derivative_sub, derivative_X, derivative_C,
      derivative_ofNat, eval_add, eval_mul, eval_sub, eval_one, eval_zero,
      eval_ofNat, eval_X, eval_C, hallPolynomial_eval] at hd
    simp only [chebyshevBezout, History.dividedDifference, ite_true]
    simp only [Nat.cast_add, Nat.cast_one] at hd ⊢
    linarith
  · simp only [chebyshevBezout, History.dividedDifference, hxy, ite_false]
    have h := hallSum_difference n x y
    simp only [Nat.cast_add, Nat.cast_one] at h ⊢
    field_simp
    nlinarith [sub_ne_zero.mpr hxy]

end
end bezout
