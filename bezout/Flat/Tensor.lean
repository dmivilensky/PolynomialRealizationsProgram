import bezout.Flat.Factors
import bezout.Flat.Chebyshev

/-!
Article: bezout, the balancing identities after Equation (12), Appendix B.
Use: identifies the explicit convex factors as the actual Flat response factors.
Proof: adjacent reservoirs cancel in finite partial sums. The last reservoir is
one target mass, so its boundary contribution vanishes.
-/

namespace bezout.Flat
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators

/-- Finite partial-sum cancellation, including its unextracted boundary reservoir.
Use: the exact algebraic invariant of response equalization. -/
theorem tensor_partial (I : chebyshev1.SpectralInterval) (n m : ℕ) (hm : m ≤ n) (x y : ℝ) :
    (∑ j ∈ Finset.range (m + 1), unitMass I (n + 1) *
      (factorPolynomial I (n + 1) j).eval x * (queryPolynomial I (n + 1) (n - j)).eval y) =
      (∑ j ∈ Finset.range (m + 1), mass I (n + 1) j * (T ℝ j).eval x *
        (normalizedU I (n - j)).eval y) -
      (reservoir I (n + 1) m - unitMass I (n + 1)) *
        (factorPolynomial I (n + 1) m).eval x * (normalizedU I (n - m - 1)).eval y := by
  induction m with
  | zero =>
    have hq := query_balance I (n + 1) (by omega) n y
    simp only [Nat.zero_add, Finset.sum_range_one, factorPolynomial, eval_one, mul_one, T_zero,
      Nat.cast_zero, Nat.sub_zero] at hq ⊢
    have hr : reservoir I (n + 1) 0 = mass I (n + 1) 0 := by simp [reservoir, prefixMass]
    simp only [Nat.add_sub_cancel, Nat.sub_self, hr] at hq ⊢
    exact hq
  | succ m ih =>
    rw [Finset.sum_range_succ,
      Finset.sum_range_succ (fun j => mass I (n + 1) j * (T ℝ j).eval x * (normalizedU I (n - j)).eval y),
      ih (by omega)]
    have hq := query_balance I (n + 1) (by omega) (n - (m + 1)) y
    have hf := factor_balance I (n + 1) (by omega) (m + 1) (by omega) x
    have hindex : n - (n - (m + 1)) = m + 1 := by omega
    have hpred : n - m - 1 = n - (m + 1) := by omega
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false,
      Nat.add_sub_cancel] at hq hf
    rw [hindex] at hq
    rw [hpred]
    linear_combination (factorPolynomial I (n + 1) (m + 1)).eval x * hq +
      (normalizedU I (n - (m + 1))).eval y * hf

/-- Every source term is the corresponding Hall Chebyshev tensor term.
Use: relates the normalized construction to the unconditional Bezoutian expansion. -/
theorem source_hall (I : chebyshev1.SpectralInterval) (n j : ℕ) :
    mass I (n + 1) j * (T ℝ j).eval (1 : ℝ) =
      hallTerm j 1 * (U ℝ ((n - j : ℕ) : ℤ)).eval I.eta := by
  by_cases hj : j = 0
  · subst j; simp [mass, hallTerm, u]; ring
  · simp [mass, hallTerm, hj, u]

/-- The explicit Flat factors preserve the entire Chebyshev tensor.
Use: determines every actual response polynomial by factor uniqueness. -/
theorem tensor_identity_range (I : chebyshev1.SpectralInterval) (n : ℕ) (x y : ℝ) :
    (∑ j ∈ Finset.range (n + 1), unitMass I (n + 1) *
      (factorPolynomial I (n + 1) j).eval x * (queryPolynomial I (n + 1) (n - j)).eval y) =
      chebyshevBezout (n + 1) x y := by
  rw [tensor_partial I n n (le_refl n),
    show reservoir I (n + 1) n = unitMass I (n + 1) by
      simpa only [Nat.add_sub_cancel] using reservoir_last I (n + 1) (by omega)]
  simp only [sub_self, zero_mul, sub_zero]
  rw [hall_expansion]
  apply Finset.sum_congr rfl
  intro j _
  have hu := ne_of_gt (u_pos I (n - j))
  by_cases hj : j = 0
  · subst j
    simp only [Nat.sub_zero] at hu
    simp only [mass, ite_true, Nat.add_sub_cancel, Nat.sub_zero, Nat.cast_zero,
      T_zero, eval_one, mul_one, normalizedU, eval_mul, eval_C, hallTerm]
    change u I n / 2 * (1 / u I n * (U ℝ n).eval y) = 1 / 2 * (U ℝ n).eval y
    field_simp
  · simp only [mass, hj, ite_false, Nat.add_sub_cancel, normalizedU, eval_mul, eval_C, hallTerm]
    field_simp

/-- Exact source-mass normalization from the Hall tensor at one and eta.
Use: converts the common response mass to the article's physical S_N/N. -/
theorem totalMass_formula (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 0 < N) :
    totalMass I N = (I.den N - 1) / (2 * (I.eta - 1)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  have ht : totalMass I (n + 1) = hallSum n 1 I.eta := by
    unfold totalMass prefixMass hallSum
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro j _
    simpa only [T_eval_one, mul_one] using source_hall I n j
  rw [ht, ← hall_expansion]
  have he : (1 : ℝ) ≠ I.eta := ne_of_lt I.eta_gt_one
  simp only [chebyshevBezout, History.dividedDifference, he, ite_false, T_eval_one]
  change (1 - I.den (n + 1)) / (1 - I.eta) / 2 = (I.den (n + 1) - 1) / (2 * (I.eta - 1))
  field_simp [ne_of_gt (sub_pos.mpr I.eta_gt_one)]
  ring

end
end bezout.Flat
