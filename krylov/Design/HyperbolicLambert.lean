import jacobi.Young.Hyperbolic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

/-!
Article: main_krylov, apC:lem:poisson, the convergent hyperbolic dual series.
Use: prove summability, positivity, explicit bounds and leading exponential
asymptotics for the actual Lambert series underlying both Poisson remainders.
Source: elementary geometric-series estimates; the hyperbolic secant itself
is reused from the earlier jacobi formalization.
-/

namespace krylov.Design
noncomputable section
open Filter Real jacobi.Young
open scoped Topology

/-- The actual positive Lambert series for half the sampled hyperbolic secant sum.
Article: main_krylov, apC:lem:poisson, q=exp(-theta). -/
def sechLambert (q : ℝ) : ℝ := ∑' n : ℕ, q ^ (n + 1) / (1 + q ^ (2 * (n + 1)))

/-- The actual positive Lambert series for half the weighted sampled hyperbolic cosecant sum.
Article: main_krylov, apC:lem:poisson. -/
def cschLambert (q : ℝ) : ℝ :=
  ∑' n : ℕ, ((n : ℝ) + 1) * q ^ (n + 1) / (1 - q ^ (2 * (n + 1)))

/-- The shifted geometric series has its actual exact sum.
Article: main_krylov, apC:lem:poisson. -/
theorem hasSum_shifted_geometric {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    HasSum (fun n : ℕ => q ^ (n + 1)) (q / (1 - q)) := by
  convert! (hasSum_geometric_of_lt_one hq₀ hq₁).mul_left q using 1
  funext n
  ring

/-- The shifted linearly weighted geometric series has its actual exact sum.
Article: main_krylov, apC:lem:poisson. -/
theorem hasSum_shifted_weighted_geometric {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) * q ^ (n + 1)) (q / (1 - q) ^ 2) := by
  have hnorm : ‖q‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hq₀]
  convert! ((hasSum_coe_mul_geometric_of_norm_lt_one hnorm).add
    (hasSum_geometric_of_lt_one hq₀ hq₁)).mul_left q using 1
  · funext n
    simp only [pow_succ]
    ring
  · field_simp
    ring

/-- The secant Lambert series is genuinely summable on the full nome interval.
Article: main_krylov, apC:lem:poisson. -/
theorem sechLambert_summable {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    Summable (fun n : ℕ => q ^ (n + 1) / (1 + q ^ (2 * (n + 1)))) := by
  apply Summable.of_nonneg_of_le (fun n => by positivity) _
    (hasSum_shifted_geometric hq₀ hq₁).summable
  intro n
  exact div_le_self (pow_nonneg hq₀ _) (le_add_of_nonneg_right (pow_nonneg hq₀ _))

/-- The secant Lambert series lies between its first term and the full geometric majorant.
Article: main_krylov, apC:lem:poisson, quantitative positive remainder bounds. -/
theorem sechLambert_bounds {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    q / (1 + q ^ 2) ≤ sechLambert q ∧ sechLambert q ≤ q / (1 - q) := by
  constructor
  · simpa only [Nat.zero_add, pow_one, Nat.mul_one, sechLambert] using!
      (sechLambert_summable hq₀ hq₁).le_tsum 0 (fun n _ => by positivity)
  · exact ((sechLambert_summable hq₀ hq₁).tsum_le_tsum
      (fun n => div_le_self (pow_nonneg hq₀ _) (le_add_of_nonneg_right (pow_nonneg hq₀ _)))
      (hasSum_shifted_geometric hq₀ hq₁).summable).trans_eq
        (hasSum_shifted_geometric hq₀ hq₁).tsum_eq

/-- Every weighted-cosecant denominator is bounded below by the first denominator.
Article: main_krylov, apC:lem:poisson. -/
theorem cschLambert_term_bound {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) (n : ℕ) :
    0 ≤ ((n : ℝ) + 1) * q ^ (n + 1) / (1 - q ^ (2 * (n + 1))) ∧
    ((n : ℝ) + 1) * q ^ (n + 1) / (1 - q ^ (2 * (n + 1))) ≤
      (1 - q ^ 2)⁻¹ * (((n : ℝ) + 1) * q ^ (n + 1)) := by
  have hp : q ^ (2 * (n + 1)) ≤ q ^ 2 := pow_le_pow_of_le_one hq₀ hq₁.le (by omega)
  have hq2 : q ^ 2 < 1 := pow_lt_one₀ hq₀ hq₁ (by omega)
  constructor
  · exact div_nonneg (by positivity) (by linarith)
  · rw [mul_comm ((1 - q ^ 2)⁻¹), ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)

/-- The weighted-cosecant Lambert series is genuinely summable throughout the nome interval.
Article: main_krylov, apC:lem:poisson. -/
theorem cschLambert_summable {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * q ^ (n + 1) / (1 - q ^ (2 * (n + 1)))) :=
  Summable.of_nonneg_of_le (fun n => (cschLambert_term_bound hq₀ hq₁ n).1)
    (fun n => (cschLambert_term_bound hq₀ hq₁ n).2)
    ((hasSum_shifted_weighted_geometric hq₀ hq₁).summable.mul_left ((1 - q ^ 2)⁻¹))

/-- The weighted-cosecant Lambert sum has explicit matching first-order bounds.
Article: main_krylov, apC:lem:poisson, quantitative positive remainder bounds. -/
theorem cschLambert_bounds {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    q / (1 - q ^ 2) ≤ cschLambert q ∧
      cschLambert q ≤ (1 - q ^ 2)⁻¹ * (q / (1 - q) ^ 2) := by
  constructor
  · simpa only [Nat.zero_add, Nat.cast_zero, zero_add, pow_one, Nat.mul_one, one_mul, cschLambert] using!
      (cschLambert_summable hq₀ hq₁).le_tsum 0
        (fun n _ => (cschLambert_term_bound hq₀ hq₁ n).1)
  · have hs := ((hasSum_shifted_weighted_geometric hq₀ hq₁).mul_left ((1 - q ^ 2)⁻¹))
    exact ((cschLambert_summable hq₀ hq₁).tsum_le_tsum
      (fun n => (cschLambert_term_bound hq₀ hq₁ n).2) hs.summable).trans_eq hs.tsum_eq

/-- The sampled secant Lambert series has leading term q as the nome tends to zero.
Article: main_krylov, apC:lem:poisson, the first exponential remainder coefficient. -/
theorem sechLambert_ratio_tendsto_one :
    Tendsto (fun q : ℝ => sechLambert q / q) (𝓝[>] 0) (𝓝 1) := by
  have hlo : Tendsto (fun q : ℝ => 1 / (1 + q ^ 2)) (𝓝[>] 0) (𝓝 1) := by
    convert! (continuousAt_const.div (continuousAt_const.add (continuousAt_id.pow 2))
      (by norm_num : (1 : ℝ) + 0 ^ 2 ≠ 0)).tendsto.mono_left nhdsWithin_le_nhds using 1
    norm_num
  have hhi : Tendsto (fun q : ℝ => 1 / (1 - q)) (𝓝[>] 0) (𝓝 1) := by
    convert! (continuousAt_const.div (continuousAt_const.sub continuousAt_id)
      (by norm_num : (1 : ℝ) - 0 ≠ 0)).tendsto.mono_left nhdsWithin_le_nhds using 1
    norm_num
  have hq : ∀ᶠ q : ℝ in 𝓝[>] 0, 0 < q ∧ q < 1 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds] with q hq hq1
    exact ⟨hq, hq1⟩
  apply hlo.squeeze' hhi
  · filter_upwards [hq] with q hq
    have h := div_le_div_of_nonneg_right (sechLambert_bounds hq.1.le hq.2).1 hq.1.le
    have he : (q / (1 + q ^ 2)) / q = 1 / (1 + q ^ 2) := by field_simp [hq.1.ne']
    rwa [he] at h
  · filter_upwards [hq] with q hq
    have h := div_le_div_of_nonneg_right (sechLambert_bounds hq.1.le hq.2).2 hq.1.le
    have he : (q / (1 - q)) / q = 1 / (1 - q) := by field_simp [hq.1.ne']
    rwa [he] at h

/-- The sampled weighted-cosecant Lambert series also has leading term q as the nome tends to zero.
Article: main_krylov, apC:lem:poisson, the second exponential remainder coefficient. -/
theorem cschLambert_ratio_tendsto_one :
    Tendsto (fun q : ℝ => cschLambert q / q) (𝓝[>] 0) (𝓝 1) := by
  have hlo : Tendsto (fun q : ℝ => 1 / (1 - q ^ 2)) (𝓝[>] 0) (𝓝 1) := by
    convert! (continuousAt_const.div (continuousAt_const.sub (continuousAt_id.pow 2))
      (by norm_num : (1 : ℝ) - 0 ^ 2 ≠ 0)).tendsto.mono_left nhdsWithin_le_nhds using 1
    norm_num
  have hhi : Tendsto (fun q : ℝ => (1 - q ^ 2)⁻¹ / (1 - q) ^ 2) (𝓝[>] 0) (𝓝 1) := by
    have hc : ContinuousAt (fun q : ℝ => (1 - q ^ 2)⁻¹ / (1 - q) ^ 2) 0 :=
      ((continuousAt_const.sub (continuousAt_id.pow 2)).inv₀ (by norm_num)).div
        ((continuousAt_const.sub continuousAt_id).pow 2) (by norm_num)
    convert! hc.tendsto.mono_left nhdsWithin_le_nhds using 1
    norm_num
  have hq : ∀ᶠ q : ℝ in 𝓝[>] 0, 0 < q ∧ q < 1 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds] with q hq hq1
    exact ⟨hq, hq1⟩
  apply hlo.squeeze' hhi
  · filter_upwards [hq] with q hq
    have h := div_le_div_of_nonneg_right (cschLambert_bounds hq.1.le hq.2).1 hq.1.le
    have he : (q / (1 - q ^ 2)) / q = 1 / (1 - q ^ 2) := by field_simp [hq.1.ne']
    rwa [he] at h
  · filter_upwards [hq] with q hq
    have h := div_le_div_of_nonneg_right (cschLambert_bounds hq.1.le hq.2).2 hq.1.le
    have he : ((1 - q ^ 2)⁻¹ * (q / (1 - q) ^ 2)) / q = (1 - q ^ 2)⁻¹ / (1 - q) ^ 2 := by
      field_simp [hq.1.ne']
    rwa [he] at h

end
end krylov.Design
