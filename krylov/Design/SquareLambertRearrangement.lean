import krylov.Design.SechLatticeSquare

/-!
Article: main_krylov, apC:lem:poisson, the actual Lambert rearrangement behind AGM duplication.
Use: prove the squared-secant Lambert identity by a genuinely absolutely
summable double geometric series. The joint majorant is explicitly the product
of a geometric and a linearly weighted geometric series, so Fubini is derived.
Source: differentiated geometric series and unconditional Fubini in mathlib.
-/

namespace krylov.Design
noncomputable section
open Real Filter jacobi.Young

/-- The genuine squared-secant Lambert series in nome q=exp(-2*theta).
Article: main_krylov, apC:lem:poisson. -/
def squareLambert (q : ℝ) : ℝ := ∑' n : ℕ, q ^ (n + 1) / (1 + q ^ (n + 1)) ^ 2

/-- The actual signed divisor Lambert series arising from geometric differentiation.
Article: main_krylov, apC:lem:poisson. -/
def signedDivisorLambert (q : ℝ) : ℝ :=
  ∑' k : ℕ, (-1 : ℝ) ^ (k + 1) * ((k : ℝ) + 1) * q ^ (k + 1) / (1 - q ^ (k + 1))

/-- The exact shifted weighted geometric sum for every real ratio of norm less than one.
Article: main_krylov, apC:lem:poisson, legitimate signed geometric expansion. -/
theorem hasSum_shifted_weighted_geometric_norm {r : ℝ} (hr : ‖r‖ < 1) :
    HasSum (fun k : ℕ => ((k : ℝ) + 1) * r ^ (k + 1)) (r / (1 - r) ^ 2) := by
  convert! ((hasSum_coe_mul_geometric_of_norm_lt_one hr).add
    (hasSum_geometric_of_norm_lt_one hr)).mul_left r using 1
  · funext k
    simp only [pow_succ]
    ring
  · field_simp
    ring

/-- The actual signed geometric double series has a concrete summable product majorant.
Article: main_krylov, apC:lem:poisson, the justified Fubini step. -/
theorem squareLambert_double_summable {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    Summable (fun p : ℕ × ℕ => -(((p.2 : ℝ) + 1) * (-q ^ (p.1 + 1)) ^ (p.2 + 1))) := by
  have hnorm : ‖q‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hq₀] using hq₁
  have hA := (hasSum_shifted_geometric hq₀ hq₁).summable
  have hB : Summable (fun k : ℕ => ((k : ℝ) + 1) * q ^ k) := by
    convert! ((hasSum_coe_mul_geometric_of_norm_lt_one hnorm).add
      (hasSum_geometric_of_lt_one hq₀ hq₁)).summable using 1
    funext k
    ring
  have hmajor := hA.mul_of_nonneg hB (fun _ => pow_nonneg hq₀ _)
    (fun k => mul_nonneg (by positivity) (pow_nonneg hq₀ _))
  apply hmajor.of_norm_bounded
  rintro ⟨n, k⟩
  rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (k : ℝ) + 1),
    abs_pow, abs_neg, abs_of_nonneg (pow_nonneg hq₀ _), ← pow_mul]
  calc
    ((k : ℝ) + 1) * q ^ ((n + 1) * (k + 1)) ≤ ((k : ℝ) + 1) * q ^ ((n + 1) + k) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hq₀ hq₁.le (by nlinarith)) (by positivity)
    _ = q ^ (n + 1) * (((k : ℝ) + 1) * q ^ k) := by rw [pow_add]; ring

/-- The genuine squared-secant Lambert series equals the actual negative signed divisor series.
Article: main_krylov, apC:lem:poisson, the critical geometric rearrangement.
Proof: rows are the differentiated geometric sum at -q^(n+1); columns are
ordinary geometric sums. The independently proved joint summability justifies exchange. -/
theorem squareLambert_eq_neg_signedDivisor {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    squareLambert q = -signedDivisorLambert q := by
  let H : ℕ → ℕ → ℝ := fun n k => -(((k : ℝ) + 1) * (-q ^ (n + 1)) ^ (k + 1))
  have hs : Summable (Function.uncurry H) := squareLambert_double_summable hq₀ hq₁
  have hrow (n : ℕ) : (∑' k : ℕ, H n k) = q ^ (n + 1) / (1 + q ^ (n + 1)) ^ 2 := by
    have hp : q ^ (n + 1) < 1 := pow_lt_one₀ hq₀ hq₁ (by omega)
    have hn : ‖-q ^ (n + 1)‖ < 1 := by
      simpa only [Real.norm_eq_abs, abs_neg, abs_of_nonneg (pow_nonneg hq₀ _)] using hp
    have h := (hasSum_shifted_weighted_geometric_norm hn).neg
    simpa only [H, sub_neg_eq_add, neg_div, neg_neg] using h.tsum_eq
  have hcol (k : ℕ) : (∑' n : ℕ, H n k) =
      -((-1 : ℝ) ^ (k + 1) * ((k : ℝ) + 1) * q ^ (k + 1) / (1 - q ^ (k + 1))) := by
    have hp : q ^ (k + 1) < 1 := pow_lt_one₀ hq₀ hq₁ (by omega)
    have he (n : ℕ) : H n k =
        -((-1 : ℝ) ^ (k + 1) * ((k : ℝ) + 1)) * (q ^ (k + 1)) ^ (n + 1) := by
      dsimp [H]
      rw [neg_pow, ← pow_mul, ← pow_mul, Nat.mul_comm (n + 1) (k + 1)]
      ring
    simp_rw [he]
    rw [tsum_mul_left, (hasSum_shifted_geometric (pow_nonneg hq₀ _) hp).tsum_eq]
    ring
  unfold squareLambert signedDivisorLambert
  calc
    (∑' n : ℕ, q ^ (n + 1) / (1 + q ^ (n + 1)) ^ 2) = ∑' n : ℕ, ∑' k : ℕ, H n k :=
      tsum_congr (fun n => (hrow n).symm)
    _ = ∑' k : ℕ, ∑' n : ℕ, H n k := hs.tsum_comm.symm
    _ = ∑' k : ℕ, -((-1 : ℝ) ^ (k + 1) * ((k : ℝ) + 1) * q ^ (k + 1) / (1 - q ^ (k + 1))) :=
      tsum_congr hcol
    _ = _ := tsum_neg

end
end krylov.Design
