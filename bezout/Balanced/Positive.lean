import bezout.Balanced.Basis

/-!
Article: bezout, positivity of both Balanced parity factors.
Use: certifies nonnegative first-kind Chebyshev coefficients without choosing
an irrelevant padded coefficient vector. This cone also proves the common
endpoint simultaneously attains every spectral polynomial bound.
-/

namespace bezout.Balanced
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators

/-- Finite nonnegative first-kind Chebyshev combinations. -/
inductive ChebPositive : ℝ[X] → Prop
  | zero : ChebPositive 0
  | term (n : ℕ) : ChebPositive (T ℝ n)
  | add {p q : ℝ[X]} : ChebPositive p → ChebPositive q → ChebPositive (p + q)
  | scale {p : ℝ[X]} (a : ℝ) : 0 ≤ a → ChebPositive p → ChebPositive (C a * p)

/-- A nonnegative Chebyshev combination is bounded by its endpoint coefficient mass. -/
theorem ChebPositive.bound {p : ℝ[X]} (hp : ChebPositive p) {x : ℝ}
    (hx : |x| ≤ 1) : |p.eval x| ≤ p.eval 1 := by
  induction hp with
  | zero => simp
  | term n => simpa using abs_eval_T_real_le_one (n : ℤ) hx
  | add hp hq ihp ihq =>
    simp only [eval_add]
    exact (abs_add_le _ _).trans (add_le_add ihp ihq)
  | scale a ha _ ih =>
    simp only [eval_mul, eval_C, abs_mul, abs_of_nonneg ha]
    exact mul_le_mul_of_nonneg_left ih ha

/-- Endpoint mass of a nonnegative Chebyshev combination is nonnegative. -/
theorem ChebPositive.endpoint_nonneg {p : ℝ[X]} (hp : ChebPositive p) : 0 ≤ p.eval 1 :=
  (abs_nonneg _).trans (hp.bound (x := 1) (by norm_num))

/-- Finite sums preserve nonnegative Chebyshev coefficients. -/
theorem ChebPositive.sum {ι : Type*} (S : Finset ι) (p : ι → ℝ[X])
    (hp : ∀ i ∈ S, ChebPositive (p i)) : ChebPositive (∑ i ∈ S, p i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using ChebPositive.zero
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact ChebPositive.add (hp i (by simp)) (ih (by intro j hj; exact hp j (by simp [hj])))

/-- Every second-kind Chebyshev polynomial has nonnegative first-kind coefficients. -/
theorem U_positive (r : ℕ) : ChebPositive (U ℝ r) := by
  induction r using Nat.twoStepInduction with
  | zero => simpa using ChebPositive.term 0
  | one => simpa only [Nat.cast_one, U_one, T_one, C_ofNat] using ChebPositive.scale 2 (by norm_num) (ChebPositive.term 1)
  | more r ih _ =>
    have h := U_eq_two_mul_T_add_U ℝ (r : ℤ)
    norm_cast at h
    rw [h]
    apply ChebPositive.add _ ih
    simpa only [C_ofNat, Nat.cast_add, Nat.cast_ofNat] using ChebPositive.scale 2 (by norm_num) (ChebPositive.term (r + 2))

/-- Second-kind differences along one parity retain nonnegative coefficients. -/
theorem U_difference_positive (r k : ℕ) : ChebPositive (U ℝ ((r + 2 * k : ℕ) : ℤ) - U ℝ r) := by
  induction k with
  | zero => simpa using ChebPositive.zero
  | succ k ih =>
    have h := U_eq_two_mul_T_add_U ℝ ((r + 2 * k : ℕ) : ℤ)
    have hi : r + 2 * (k + 1) = (r + 2 * k) + 2 := by omega
    rw [hi]
    norm_cast at h
    rw [h]
    have he : 2 * T ℝ (((r + 2 * k) + 2 : ℕ) : ℤ) + U ℝ ((r + 2 * k : ℕ) : ℤ) - U ℝ r =
        2 * T ℝ (((r + 2 * k) + 2 : ℕ) : ℤ) + (U ℝ ((r + 2 * k : ℕ) : ℤ) - U ℝ r) := by ring
    rw [he]
    apply ChebPositive.add _ ih
    simpa only [C_ofNat] using ChebPositive.scale 2 (by norm_num) (ChebPositive.term ((r + 2 * k) + 2))

/-- Ordered second-kind degrees of the same parity have a positive difference. -/
theorem U_sub_positive {r R : ℕ} (hle : r ≤ R) (hp : r % 2 = R % 2) :
    ChebPositive (U ℝ R - U ℝ r) := by
  have he : R = r + 2 * ((R - r) / 2) := by omega
  rw [he]
  exact U_difference_positive r ((R - r) / 2)

/-- Every lower-degree query remainder has nonnegative Chebyshev coefficients. -/
theorem remainder_positive {N s : ℕ} (hN : 2 ≤ N) (hs : s < N) :
    ChebPositive (remainder N s) := by
  induction s using Nat.twoStepInduction with
  | zero => exact ChebPositive.zero
  | one => exact ChebPositive.zero
  | more s ih _ =>
    rw [remainder]
    exact ChebPositive.add (ih (by omega))
      (ChebPositive.scale _ (sub_nonneg.mpr (omega_add_two_le hN hs)) (ChebPositive.term s))

/-- Both sides of the Balanced factorization have nonnegative Chebyshev coefficients. -/
theorem psi_positive {N s : ℕ} (hN : 2 ≤ N) (hs : s < N) : ChebPositive (psi N s) :=
  ChebPositive.add (remainder_positive hN hs)
    (ChebPositive.scale _ (omega_pos hN hs).le (ChebPositive.term s))

end
end bezout.Balanced
