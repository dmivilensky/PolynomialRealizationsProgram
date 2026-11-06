import nesterov.Spectral.Feasibility
import polyak.Spectral.Interior

/-! A strict minimizer reserve controls all sufficiently large lags, for arbitrary
continuous amplitudes. The bound is uniform in the frequency and does not
assume atomicity of the probability spectrum. -/
noncomputable section
open MeasureTheory
namespace nesterov.Attainment
open Spectral

def gapMap (a : SymbolPair) : C(Frequency, ℝ) := ⟨g a, continuous_g a⟩
def skewMap (a : SymbolPair) : C(Frequency, ℝ) := ⟨skew a, continuous_skew a⟩

theorem meanA_eq_cosh_sub (ν : Spectrum) (a : SymbolPair) (t : ℝ) (n : ℕ) :
    meanA ν a t n = meanG ν a * Real.cosh (n*t) -
      ∫ c, g a c * Real.cos (n*Real.arccos c) ∂ν := by
  have hG := polyak.Spectral.integrable_continuous ν (continuous_g a)
  have hcos := polyak.Spectral.integrable_continuous ν (show Continuous
    (fun c : Frequency => g a c * Real.cos (n*Real.arccos c)) by unfold g; fun_prop)
  unfold meanA lagA meanG
  simp_rw [mul_sub]
  rw [integral_sub (hG.mul_const _) hcos, integral_mul_const]

theorem abs_cos_moment_le (ν : Spectrum) (a : SymbolPair) (n : ℕ) :
    |∫ c, g a c * Real.cos (n*Real.arccos c) ∂ν| ≤ ‖gapMap a‖ := by
  change ‖∫ c, g a c * Real.cos (n*Real.arccos c) ∂ν‖ ≤ _
  have hb (c : Frequency) : ‖g a c * Real.cos (n*Real.arccos c)‖ ≤ ‖gapMap a‖ := by
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (show ‖Real.cos (n*Real.arccos c)‖ ≤ 1 by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one _) ).trans
      (by simpa only [gapMap, ContinuousMap.coe_mk] using (gapMap a).norm_coe_le_norm c)
  simpa using norm_integral_le_of_norm_le_const (μ := (ν : Measure Frequency))
    (Filter.Eventually.of_forall hb)

theorem abs_meanB_le (ν : Spectrum) (a : SymbolPair) (n : ℕ) :
    |meanB ν a n| ≤ 2 * ‖skewMap a‖ := by
  change ‖∫ c, lagB a n c ∂ν‖ ≤ _
  have hb (c : Frequency) : ‖lagB a n c‖ ≤ 2 * ‖skewMap a‖ := by
    simp only [lagB, norm_mul]
    rw [show ‖(2 : ℝ)‖ = 2 by norm_num]
    calc
      2 * ‖skew a c‖ * ‖Real.sin (n*Real.arccos c)‖ ≤ 2 * ‖skew a c‖ :=
        mul_le_of_le_one_right (by positivity) (show ‖Real.sin (n*Real.arccos c)‖ ≤ 1 by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one _)
      _ ≤ _ := mul_le_mul_of_nonneg_left ((skewMap a).norm_coe_le_norm c) (by norm_num)
  simpa using norm_integral_le_of_norm_le_const (μ := (ν : Measure Frequency))
    (Filter.Eventually.of_forall hb)

/-- Both raw lag inequalities have the same explicit lower bound. -/
theorem raw_lag_lower_bounds (ν : Spectrum) (a : SymbolPair) (C t : ℝ) (n : ℕ) :
    (meanG ν a-|C|)*Real.cosh (n*t)-‖gapMap a‖-2*‖skewMap a‖ ≤
      meanA ν a t n-meanB ν a n+C*Real.sinh (n*t) ∧
    (meanG ν a-|C|)*Real.cosh (n*t)-‖gapMap a‖-2*‖skewMap a‖ ≤
      meanA ν a t n+meanB ν a n-C*Real.sinh (n*t) := by
  have hc := abs_le.mp (abs_cos_moment_le ν a n)
  have hb := abs_le.mp (abs_meanB_le ν a n)
  have hC : |C*Real.sinh (n*t)| ≤ |C| * Real.cosh (n*t) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (polyak.Boundary.abs_sinh_le_cosh _) (abs_nonneg _)
  have hC' := abs_le.mp hC
  rw [meanA_eq_cosh_sub]
  constructor <;> nlinarith

/-- A positive minimizer reserve leaves only finitely many possibly active lags. -/
theorem active_lags_bounded (ν : Spectrum) (a : SymbolPair) {C t : ℝ}
    (hstar : |C| < meanG ν a) (ht : t ≠ 0) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      0 < meanA ν a t n-meanB ν a n+C*Real.sinh (n*t) ∧
      0 < meanA ν a t n+meanB ν a n-C*Real.sinh (n*t) := by
  let η := meanG ν a-|C|
  let K := ‖gapMap a‖+2*‖skewMap a‖
  have hη : 0 < η := sub_pos.mpr hstar
  have ht' : 0 < |t| := abs_pos.mpr ht
  obtain ⟨N,hN⟩ := exists_nat_gt ((2*K+2)/(η*|t|))
  have hlarge : 2*K+2 < (N : ℝ)*(η*|t|) := (div_lt_iff₀ (mul_pos hη ht')).mp hN
  refine ⟨N, fun n hn => ?_⟩
  have hn' : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
  have hh := polyak.Spectral.abs_le_two_cosh ((n : ℝ)*t)
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)] at hh
  have hb : K < η*Real.cosh (n*t) := by
    have he := mul_le_mul_of_nonneg_right hn' (mul_pos hη ht').le
    have hc := mul_le_mul_of_nonneg_left hh hη.le
    nlinarith
  have hraw := raw_lag_lower_bounds ν a C t n
  constructor <;> dsimp [η,K] at hb <;> linarith [hraw.1,hraw.2]

end nesterov.Attainment
