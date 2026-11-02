import krylov.Design.SquareLambertRearrangement

/-!
Article: main_krylov, apC:lem:poisson, squared-secant duplication by real Lambert series.
Use: prove the actual signed Lambert difference, then identify it with the
genuine squared-sech and weighted-cosecant samples. Every signed series has
its independently derived absolute convergence.
Source: the proved double-geometric Fubini identity and elementary nome algebra.
-/

namespace krylov.Design
noncomputable section
open Real Filter jacobi.Young

/-- The genuine signed weighted-cosecant Lambert series.
Article: main_krylov, apC:lem:poisson. -/
def signedCschLambert (q : ℝ) : ℝ :=
  ∑' k : ℕ, (-1 : ℝ) ^ (k + 1) *
    (((k : ℝ) + 1) * q ^ (k + 1) / (1 - q ^ (2 * (k + 1))))

/-- The actual signed divisor Lambert series is absolutely summable.
Article: main_krylov, apC:lem:poisson. -/
theorem signedDivisorLambert_summable {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    Summable (fun k : ℕ => (-1 : ℝ) ^ (k + 1) * ((k : ℝ) + 1) * q ^ (k + 1) / (1 - q ^ (k + 1))) := by
  apply ((hasSum_shifted_weighted_geometric hq₀ hq₁).summable.mul_left ((1 - q)⁻¹)).of_norm_bounded
  intro k
  have hp : q ^ (k + 1) < 1 := pow_lt_one₀ hq₀ hq₁ (by omega)
  have hpq : q ^ (k + 1) ≤ q := by
    simpa only [pow_one] using pow_le_pow_of_le_one hq₀ hq₁.le (by omega : 1 ≤ k + 1)
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    one_mul, abs_of_nonneg (by positivity : 0 ≤ (k : ℝ) + 1),
    abs_of_nonneg (pow_nonneg hq₀ _), abs_of_pos (sub_pos.mpr hp)]
  rw [mul_comm ((1 - q)⁻¹), ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left (by positivity) (sub_pos.mpr hq₁) (by linarith)

/-- The actual signed weighted-cosecant Lambert series is absolutely summable.
Article: main_krylov, apC:lem:poisson. -/
theorem signedCschLambert_summable {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    Summable (fun k : ℕ => (-1 : ℝ) ^ (k + 1) *
      (((k : ℝ) + 1) * q ^ (k + 1) / (1 - q ^ (2 * (k + 1))))) := by
  apply (cschLambert_summable hq₀ hq₁).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (cschLambert_term_bound hq₀ hq₁ k).1]

/-- The genuine squared-secant Lambert difference is the actual signed weighted-cosecant series.
Article: main_krylov, apC:lem:poisson, the critical duplication rearrangement. -/
theorem squareLambert_difference {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    squareLambert (q ^ 2) - squareLambert q = signedCschLambert q := by
  have hq2 : q ^ 2 < 1 := pow_lt_one₀ hq₀ hq₁ (by norm_num)
  rw [squareLambert_eq_neg_signedDivisor (sq_nonneg q) hq2,
    squareLambert_eq_neg_signedDivisor hq₀ hq₁]
  rw [show -signedDivisorLambert (q ^ 2) - -signedDivisorLambert q =
    signedDivisorLambert q - signedDivisorLambert (q ^ 2) by ring]
  unfold signedDivisorLambert signedCschLambert
  rw [← (signedDivisorLambert_summable hq₀ hq₁).tsum_sub
    (signedDivisorLambert_summable (sq_nonneg q) hq2)]
  apply tsum_congr
  intro k
  have hp : q ^ (k + 1) < 1 := pow_lt_one₀ hq₀ hq₁ (by omega)
  have hp2 : (q ^ (k + 1)) ^ 2 < 1 := pow_lt_one₀ (pow_nonneg hq₀ _) hp (by norm_num)
  have he : (q ^ 2) ^ (k + 1) = (q ^ (k + 1)) ^ 2 := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 (k + 1)]
  have he2 : q ^ (2 * (k + 1)) = (q ^ (k + 1)) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm (k + 1) 2]
  rw [he, he2]
  field_simp [(sub_pos.mpr hp).ne', (sub_pos.mpr hp2).ne']
  ring

/-- The actual squared-sech samples equal four times their genuine Lambert series.
Article: main_krylov, apC:lem:poisson, q=exp(-2*theta). -/
theorem sampledSechSquared_eq_squareLambert (θ : ℝ) :
    sampledSechSquared θ = 4 * squareLambert (exp (-(2 * θ))) := by
  unfold sampledSechSquared squareLambert
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [sech_exp_nome, div_pow, mul_pow]
  have he : exp (-(((n : ℝ) + 1) * θ)) ^ 2 = exp (-(2 * θ)) ^ (n + 1) := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [he]
  norm_num only [sq]
  ring

/-- The actual alternating weighted-cosecant samples equal twice their signed Lambert series.
Article: main_krylov, apC:lem:poisson. -/
theorem sampledAlternatingWeightedCsch_eq_signedLambert {θ : ℝ} (hθ : 0 < θ) :
    sampledAlternatingWeightedCsch θ = 2 * signedCschLambert (exp (-θ)) := by
  unfold sampledAlternatingWeightedCsch signedCschLambert
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [sampledWeightedCsch_term hθ]
  have he : (-1 : ℝ) ^ ((n : ℤ) + 1) = (-1 : ℝ) ^ (n + 1 : ℕ) := by
    rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by omega, zpow_natCast]
  rw [he]
  ring

/-- The genuine squared-secant duplication difference is exactly the actual alternating weighted-cosecant correction.
Article: main_krylov, apC:lem:poisson, the missing hyperbolic AGM arithmetic identity. -/
theorem sampledSechSquared_duplication_difference {θ : ℝ} (hθ : 0 < θ) :
    sampledSechSquared (2 * θ) - sampledSechSquared θ =
      2 * sampledAlternatingWeightedCsch (2 * θ) := by
  have hq0 : 0 ≤ exp (-(2 * θ)) := (exp_pos _).le
  have hq1 : exp (-(2 * θ)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have he : exp (-(2 * (2 * θ))) = exp (-(2 * θ)) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [sampledSechSquared_eq_squareLambert, sampledSechSquared_eq_squareLambert,
    sampledAlternatingWeightedCsch_eq_signedLambert (mul_pos (by norm_num : (0 : ℝ) < 2) hθ), he]
  have h := squareLambert_difference hq0 hq1
  linarith

end
end krylov.Design
