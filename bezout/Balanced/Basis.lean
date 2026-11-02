import bezout.Balanced.Weights
import bezout.Synthesis.Normalized

/-!
Article: bezout, Equation `eq:stopped-basis` and Algorithm 2.
Use: constructs the actual normalized graded Balanced query basis.
Proof: a two-step low-degree remainder records the nonnegative Chebyshev
mass below the leading degree. Its mass is exactly one minus the top weight.
-/

namespace bezout.Balanced
noncomputable section
open Polynomial Polynomial.Chebyshev

/-- The lower-degree part of the stopped-parity polynomial. -/
def remainder (N : ℕ) : ℕ → ℝ[X]
  | 0 => 0
  | 1 => 0
  | s + 2 => remainder N s + C (omega N s - omega N (s + 2)) * T ℝ s

/-- The unnormalized Balanced query polynomial in the Chebyshev chart. -/
def psi (N s : ℕ) : ℝ[X] := remainder N s + C (omega N s) * T ℝ s

/-- The first stopped-parity polynomial is constant one. -/
@[simp] theorem psi_zero (N : ℕ) : psi N 0 = 1 := by simp [psi, remainder]

/-- The second stopped-parity polynomial is the first Chebyshev polynomial. -/
@[simp] theorem psi_one (N : ℕ) : psi N 1 = T ℝ 1 := by simp [psi, remainder]

/-- The defining parity recurrence, with no out-of-range subtraction. -/
theorem psi_add_two (N s : ℕ) :
    psi N (s + 2) = psi N s + C (omega N (s + 2)) * (T ℝ (s + 2) - T ℝ s) := by
  simp only [psi, remainder, C_sub, Nat.cast_add, Nat.cast_ofNat]
  ring

/-- The remainder has strictly lower degree than its query index. -/
theorem remainder_degree_lt (N s : ℕ) : (remainder N s).degree < (s : WithBot ℕ) := by
  induction s using Nat.twoStepInduction with
  | zero => simp [remainder]
  | one => simp [remainder]
  | more s ih _ =>
    simp only [remainder]
    apply lt_of_le_of_lt (degree_add_le _ _)
    apply max_lt
    · exact ih.trans (by exact_mod_cast (show s < s + 2 by omega))
    · by_cases hw : omega N s - omega N (s + 2) = 0
      · simp only [hw, C_0, zero_mul, degree_zero]
        exact WithBot.bot_lt_coe _
      · rw [degree_C_mul hw, degree_T]
        exact_mod_cast (show s < s + 2 by omega)

/-- Every valid stopped-parity query has its full prescribed degree. -/
theorem psi_degree {N s : ℕ} (hN : 2 ≤ N) (hs : s < N) :
    (psi N s).degree = (s : WithBot ℕ) := by
  have hd : (C (omega N s) * T ℝ s).degree = (s : WithBot ℕ) := by
    rw [degree_C_mul (ne_of_gt (omega_pos hN hs)), degree_T]
    simp
  unfold psi
  rw [degree_add_eq_right_of_degree_lt (hd ▸ remainder_degree_lt N s), hd]

/-- The lower-degree coefficients have total mass one minus the top weight. -/
theorem remainder_eval_one (N s : ℕ) : (remainder N s).eval 1 = 1 - omega N s := by
  induction s using Nat.twoStepInduction with
  | zero => simp [remainder]
  | one => simp [remainder]
  | more s ih _ => simp [remainder, ih]

/-- All stopped-parity polynomials have endpoint value one. -/
@[simp] theorem psi_eval_one (N s : ℕ) : (psi N s).eval 1 = 1 := by
  simp [psi, remainder_eval_one]

/-- The remainder is bounded by its positive Chebyshev coefficient mass. -/
theorem abs_remainder_eval_le {N s : ℕ} (hN : 2 ≤ N) (hs : s < N)
    {x : ℝ} (hx : |x| ≤ 1) : |(remainder N s).eval x| ≤ 1 - omega N s := by
  induction s using Nat.twoStepInduction with
  | zero => simp [remainder]
  | one => simp [remainder]
  | more s ih _ =>
    have hprev : s < N := by omega
    have hw := omega_add_two_le hN hs
    have ht := abs_eval_T_real_le_one (s : ℤ) hx
    simp only [remainder, eval_add, eval_mul, eval_C]
    calc
      _ ≤ |(remainder N s).eval x| + |(omega N s - omega N (s + 2)) * (T ℝ s).eval x| := abs_add_le _ _
      _ = |(remainder N s).eval x| + (omega N s - omega N (s + 2)) * |(T ℝ s).eval x| := by
        rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hw)]
      _ ≤ (1 - omega N s) + (omega N s - omega N (s + 2)) * 1 :=
        add_le_add (ih hprev) (mul_le_mul_of_nonneg_left ht (sub_nonneg.mpr hw))
      _ = 1 - omega N (s + 2) := by ring

/-- The unnormalized query is uniformly bounded by one on the spectral chart. -/
theorem abs_psi_eval_le_one {N s : ℕ} (hN : 2 ≤ N) (hs : s < N)
    {x : ℝ} (hx : |x| ≤ 1) : |(psi N s).eval x| ≤ 1 := by
  have hw := (omega_pos hN hs).le
  have hr := abs_remainder_eval_le hN hs hx
  have ht := abs_eval_T_real_le_one (s : ℤ) hx
  simp only [psi, eval_add, eval_mul, eval_C]
  calc
    _ ≤ |(remainder N s).eval x| + |omega N s * (T ℝ s).eval x| := abs_add_le _ _
    _ = |(remainder N s).eval x| + omega N s * |(T ℝ s).eval x| := by rw [abs_mul, abs_of_nonneg hw]
    _ ≤ (1 - omega N s) + omega N s * 1 := add_le_add hr (mul_le_mul_of_nonneg_left ht hw)
    _ = 1 := by ring

/-- Above the right endpoint every lower-degree Chebyshev term is at least one. -/
theorem remainder_eval_ge_mass {N s : ℕ} (hN : 2 ≤ N) (hs : s < N)
    {x : ℝ} (hx : 1 ≤ x) : 1 - omega N s ≤ (remainder N s).eval x := by
  induction s using Nat.twoStepInduction with
  | zero => simp [remainder]
  | one => simp [remainder]
  | more s ih _ =>
    have hprev : s < N := by omega
    have hw := omega_add_two_le hN hs
    have ht := one_le_eval_T_real (s : ℤ) hx
    simp only [remainder, eval_add, eval_mul, eval_C]
    have hm := mul_le_mul_of_nonneg_left ht (sub_nonneg.mpr hw)
    have hp := ih hprev
    nlinarith

/-- The stopped-parity normalizing value is at least one above the interval. -/
theorem one_le_psi_eval {N s : ℕ} (hN : 2 ≤ N) (hs : s < N)
    {x : ℝ} (hx : 1 ≤ x) : 1 ≤ (psi N s).eval x := by
  have hr := remainder_eval_ge_mass hN hs hx
  have ht := one_le_eval_T_real (s : ℤ) hx
  have hm := mul_le_mul_of_nonneg_left ht (omega_pos hN hs).le
  simp only [psi, eval_add, eval_mul, eval_C]
  nlinarith

/-- The exact normalizer used by Balanced scalar preparation. -/
def normalizer (I : chebyshev1.SpectralInterval) (N s : ℕ) : ℝ := (psi N s).eval I.eta

/-- The first scalar-preparation normalizer is exactly one. -/
@[simp] theorem normalizer_zero (I : chebyshev1.SpectralInterval) (N : ℕ) :
    normalizer I N 0 = 1 := by simp [normalizer]

/-- The second scalar-preparation normalizer is exactly eta. -/
@[simp] theorem normalizer_one (I : chebyshev1.SpectralInterval) (N : ℕ) :
    normalizer I N 1 = I.eta := by simp [normalizer]

/-- Scalar preparation is exactly evaluation of the stopped-parity recurrence. -/
theorem normalizer_add_two (I : chebyshev1.SpectralInterval) (N s : ℕ) :
    normalizer I N (s + 2) = normalizer I N s + omega N (s + 2) *
      ((T ℝ (s + 2)).eval I.eta - (T ℝ s).eval I.eta) := by
  unfold normalizer
  rw [psi_add_two]
  simp only [eval_add, eval_mul, eval_C, eval_sub]

/-- Every normalizer of a valid Balanced call is positive. -/
theorem normalizer_pos (I : chebyshev1.SpectralInterval) {N s : ℕ}
    (hN : 2 ≤ N) (hs : s < N) : 0 < normalizer I N s :=
  lt_of_lt_of_le zero_lt_one (one_le_psi_eval hN hs I.eta_gt_one.le)

end
end bezout.Balanced
