import bezout.Properties.Incompatibility
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Normed

/-!
Article: bezout, Theorem 4.1 odd correction and the Flat stochastic paragraph.
Use: records explicit finite correction bounds and the nonnumeric large-horizon
limits for the two constructions; the exact parity formulas are retained.
Proof: positive square-root algebra, the strict comparison of endpoint scales,
and squeezing against the inverse square of the horizon.
-/

namespace bezout.Properties
noncomputable section
open Filter Topology Asymptotics

/-- The squared odd correction lies between one and one plus the inverse horizon square. -/
theorem linearCorrectionSq_bounds {N : ℕ} (hN : 2 ≤ N) :
    1 ≤ Lower.linearCorrectionSq N ∧ Lower.linearCorrectionSq N - 1 ≤ 1 / (N : ℝ) ^ 2 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  unfold Lower.linearCorrectionSq Lower.oddCorrectionSq
  split_ifs with hodd
  · constructor
    · have hh : 0 ≤ ((N : ℝ) - 1) / (((N : ℝ) + 1) * (N : ℝ) ^ 2) := by
        apply div_nonneg _ (by positivity)
        have hh : (2 : ℝ) ≤ N := by exact_mod_cast hN
        linarith
      linarith
    · have hp : 0 < ((N : ℝ) + 1) * (N : ℝ) ^ 2 := by positivity
      have hq : 0 < (N : ℝ) ^ 2 := by positivity
      have hd : ((N : ℝ) - 1) / (((N : ℝ) + 1) * (N : ℝ) ^ 2) ≤ 1 / (N : ℝ) ^ 2 := by
        apply (div_le_div_iff₀ hp hq).mpr
        nlinarith [sq_nonneg (N : ℝ)]
      linarith
  · constructor
    · rfl
    · simp

/-- The exact correction itself differs from one by at most the inverse horizon square. -/
theorem linearCorrection_bounds {N : ℕ} (hN : 2 ≤ N) :
    0 ≤ Real.sqrt (Lower.linearCorrectionSq N) - 1 ∧
      Real.sqrt (Lower.linearCorrectionSq N) - 1 ≤ 1 / (N : ℝ) ^ 2 := by
  have hc := linearCorrectionSq_bounds hN
  have hr := Real.one_le_sqrt.mpr hc.1
  have hs := Real.sq_sqrt (Lower.linearCorrectionSq_nonneg hN)
  constructor
  · linarith
  · have hm := mul_nonneg (Real.sqrt_nonneg (Lower.linearCorrectionSq N)) (sub_nonneg.mpr hr)
    nlinarith

/-- The exact odd/even correction has the article's O(N^-2) remainder. -/
theorem linearCorrection_sub_one_isBigO :
    (fun N : ℕ => Real.sqrt (Lower.linearCorrectionSq N) - 1) =O[atTop]
      (fun N : ℕ => 1 / (N : ℝ) ^ 2) := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (linearCorrection_bounds hN).1,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ) ^ 2), one_mul]
  exact (linearCorrection_bounds hN).2

/-- Inverse horizon squares tend to zero. -/
theorem inverse_horizon_square_tendsto_zero :
    Tendsto (fun N : ℕ => 1 / (N : ℝ) ^ 2) atTop (𝓝 0) := by
  have h : Tendsto (fun N : ℕ => (N : ℝ) ^ 2) atTop atTop :=
    (Filter.tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
  simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp h

/-- The exact parity correction tends to one on all horizons together. -/
theorem linearCorrection_tendsto_one :
    Tendsto (fun N : ℕ => Real.sqrt (Lower.linearCorrectionSq N)) atTop (𝓝 1) := by
  have hzero : Tendsto (fun N : ℕ => Real.sqrt (Lower.linearCorrectionSq N) - 1) atTop (𝓝 0) := by
    apply squeeze_zero'
    · filter_upwards [eventually_ge_atTop 2] with N hN
      exact (linearCorrection_bounds hN).1
    · filter_upwards [eventually_ge_atTop 2] with N hN
      exact (linearCorrection_bounds hN).2
    · exact inverse_horizon_square_tendsto_zero
  simpa only [sub_add_cancel, zero_add] using hzero.add_const 1

/-- The terminal Chebyshev attenuation is bounded by an explicit inverse-square majorant. -/
theorem epsilon_le_inverse_square (I : chebyshev1.SpectralInterval) {N : ℕ} (hN : 2 ≤ N) :
    I.epsilon N ≤ I.delta / (2 * I.mu * (N : ℝ) ^ 2) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmu := I.mu_pos
  have he : 0 < I.epsilon N := one_div_pos.mpr (I.den_pos N)
  have hS : Lower.additiveScale I N ≤ 1 / I.mu := by
    unfold Lower.additiveScale
    apply (div_le_div_iff_of_pos_right I.mu_pos).mpr
    linarith
  have hD := (derivativeScale_lt_additiveScale I hN).le.trans hS
  have hm := mul_le_mul_of_nonneg_right hD I.mu_pos.le
  have hd : 2 * I.epsilon N * (N : ℝ) ^ 2 * I.mu ≤ I.delta := by
    have hz : (1 / I.mu) * I.mu = 1 := one_div_mul_cancel (ne_of_gt I.mu_pos)
    rw [hz] at hm
    have hh : (2 * I.epsilon N * (N : ℝ) ^ 2 * I.mu) / I.delta ≤ 1 := by
      convert hm using 1
      unfold Lower.derivativeScale
      ring
    simpa only [one_mul] using (div_le_iff₀ I.delta_pos).mp hh
  apply (le_div_iff₀ (by positivity : 0 < 2 * I.mu * (N : ℝ) ^ 2)).mpr
  nlinarith

/-- The exact terminal attenuation tends to zero for every fixed spectral interval. -/
theorem epsilon_tendsto_zero (I : chebyshev1.SpectralInterval) :
    Tendsto (fun N : ℕ => I.epsilon N) atTop (𝓝 0) := by
  apply squeeze_zero' (g := fun N : ℕ => (I.delta / (2 * I.mu)) * (1 / (N : ℝ) ^ 2))
  · exact Eventually.of_forall (fun N => (one_div_pos.mpr (I.den_pos N)).le)
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have he := epsilon_le_inverse_square I hN
    calc
      _ ≤ I.delta / (2 * I.mu * (N : ℝ) ^ 2) := he
      _ = _ := by ring
  · simpa only [mul_zero] using
      inverse_horizon_square_tendsto_zero.const_mul (I.delta / (2 * I.mu))

/-- The additive scale converges to the inverse lower spectral endpoint. -/
theorem additiveScale_tendsto (I : chebyshev1.SpectralInterval) :
    Tendsto (fun N : ℕ => Lower.additiveScale I N) atTop (𝓝 (1 / I.mu)) := by
  simpa only [sub_zero, Lower.additiveScale] using
    (epsilon_tendsto_zero I).const_sub 1 |>.div_const I.mu

/-- The exact Flat variance coefficient has the advertised normalized asymptotic ratio. -/
theorem flat_variance_ratio_tendsto_one (I : chebyshev1.SpectralInterval) :
    Tendsto (fun N : ℕ => (Lower.additiveScale I N ^ 2 / N) /
      (1 / (I.mu ^ 2 * N))) atTop (𝓝 1) := by
  have h : Tendsto (fun N : ℕ => (1 - I.epsilon N) ^ 2) atTop (𝓝 1) := by
    simpa using ((epsilon_tendsto_zero I).const_sub 1).pow 2
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold Lower.additiveScale
  field_simp [ne_of_gt I.mu_pos, hn]

/-- The exact Flat variance coefficient is asymptotic to 1/(mu^2 N). -/
theorem flat_variance_isEquivalent (I : chebyshev1.SpectralInterval) :
    (fun N : ℕ => Lower.additiveScale I N ^ 2 / N) ~[atTop]
      (fun N : ℕ => 1 / (I.mu ^ 2 * N)) := by
  apply (Asymptotics.isEquivalent_iff_tendsto_one ?_).mpr
  · exact flat_variance_ratio_tendsto_one I
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact one_div_ne_zero (mul_ne_zero (pow_ne_zero 2 (ne_of_gt I.mu_pos)) hn)

end
end bezout.Properties
