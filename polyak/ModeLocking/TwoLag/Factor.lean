import polyak.ModeLocking.TwoLag.Polynomial
import polyak.Levels.Geometry.LagOne

/-! Exact factorization of the original two signed lag functions. -/
noncomputable section
namespace polyak.ModeLocking.TwoLag
open General Levels Set
open Spectral (chebT chebU)

def symbol (q : Tuning) (K : ℕ) (a b : ℝ) (ω : Frequency) : ℝ :=
  a*(tuningCurve q).lag 1 ω+b*(tuningCurve q).lag (-(K : ℤ)) ω

theorem polynomial_factor (q : Tuning) {K : ℕ} (hK : 0<K) (a b : ℝ)
    (ω : Frequency) (hω : 0<(ω : ℝ) ∧ (ω : ℝ)<Real.pi) :
    symbol q K a b ω = Real.sin (q.angle ω)/Real.sin (ω : ℝ)*
      (q.Xi (Real.cos (ω : ℝ))*
        (a*(1-Real.cos (ω : ℝ))+b*(1-chebT K (Real.cos (ω : ℝ))))-
        (1-Real.cos (ω : ℝ)^2)*(a-b*chebU (K-1) (Real.cos (ω : ℝ)))) := by
  rw [symbol, Farey.Certificates.lag_polynomial_factor q 1 (by norm_num) ω hω,
    Farey.Certificates.lag_polynomial_factor q (-(K : ℤ)) (by omega) ω hω,
    Farey.Certificates.signedLagPolynomial_neg q hK]
  norm_num [Farey.Certificates.signedLagPolynomial, chebT, chebU]
  ring

theorem symbol_factor (q : Tuning) {K : ℕ} (hK : 0<K) {a b : ℝ}
    (ha : 0<a) (hb : 0≤b) (ω : Frequency)
    (hω : 0<(ω : ℝ) ∧ (ω : ℝ)<Real.pi) :
    symbol q K a b ω =
      a*(Real.sin (q.angle ω)*(1-Real.cos (ω : ℝ))*
        (1+(b/a)*W K (Real.cos (ω : ℝ)))/Real.sin (ω : ℝ))*
        (q.Xi (Real.cos (ω : ℝ))-Psi K (b/a) (Real.cos (ω : ℝ))) := by
  have hd := (Psi_den_pos K (div_nonneg hb ha.le)
    ⟨Real.neg_one_le_cos (ω : ℝ), Real.cos_le_one (ω : ℝ)⟩).ne'
  rw [polynomial_factor q hK a b ω hω]
  unfold Psi
  have hW : chebT K (Real.cos (ω : ℝ)) =
      1-(1-Real.cos (ω : ℝ))*W K (Real.cos (ω : ℝ)) := by
    linarith [W_identity K (Real.cos (ω : ℝ))]
  have hd' : a+b*W K (Real.cos (ω : ℝ)) ≠ 0 := by
    exact ne_of_gt (add_pos_of_pos_of_nonneg ha
      (mul_nonneg hb (W_nonneg K ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)))
  rw [hW]
  field_simp [ha.ne', hd, hd']
  ring

theorem factor_pos (q : Tuning) (K : ℕ) {a b : ℝ} (ha : 0<a) (hb : 0≤b)
    (ω : Frequency) (hω : 0<(ω : ℝ) ∧ (ω : ℝ)<Real.pi) :
    0<a*(Real.sin (q.angle ω)*(1-Real.cos (ω : ℝ))*
      (1+(b/a)*W K (Real.cos (ω : ℝ)))/Real.sin (ω : ℝ)) := by
  apply mul_pos ha
  apply div_pos
  · apply mul_pos
    · exact mul_pos (Real.sin_pos_of_pos_of_lt_pi (q.angle_mem hω).1 (q.angle_mem hω).2)
        (sub_pos.mpr (by simpa using Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0 : ℝ) ≤ 0) hω.2.le hω.1))
    · exact Psi_den_pos K (div_nonneg hb ha.le) ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  · exact Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2

theorem symbol_nonpos_iff (q : Tuning) {K : ℕ} (hK : 0<K) {a b : ℝ}
    (ha : 0<a) (hb : 0≤b) (ω : Frequency) (hω : 0<(ω : ℝ) ∧ (ω : ℝ)<Real.pi) :
    symbol q K a b ω ≤ 0 ↔ q.Xi (Real.cos (ω : ℝ)) ≤ Psi K (b/a) (Real.cos (ω : ℝ)) := by
  rw [symbol_factor q hK ha hb ω hω, mul_nonpos_iff]
  have hp := factor_pos q K ha hb ω hω
  simp only [hp.le, not_le.mpr hp, true_and, false_and, or_false, sub_nonpos]

theorem symbol_neg_iff (q : Tuning) {K : ℕ} (hK : 0<K) {a b : ℝ}
    (ha : 0<a) (hb : 0≤b) (ω : Frequency) (hω : 0<(ω : ℝ) ∧ (ω : ℝ)<Real.pi) :
    symbol q K a b ω < 0 ↔ q.Xi (Real.cos (ω : ℝ)) < Psi K (b/a) (Real.cos (ω : ℝ)) := by
  rw [symbol_factor q hK ha hb ω hω, mul_neg_iff]
  have hp := factor_pos q K ha hb ω hω
  simp only [hp, not_lt.mpr hp.le, true_and, false_and, or_false, sub_neg]

theorem symbol_zero_iff (q : Tuning) {K : ℕ} (hK : 0<K) {a b : ℝ}
    (ha : 0<a) (hb : 0≤b) (ω : Frequency) (hω : 0<(ω : ℝ) ∧ (ω : ℝ)<Real.pi) :
    symbol q K a b ω = 0 ↔ q.Xi (Real.cos (ω : ℝ)) = Psi K (b/a) (Real.cos (ω : ℝ)) := by
  rw [symbol_factor q hK ha hb ω hω, mul_eq_zero]
  simp only [(factor_pos q K ha hb ω hω).ne', false_or, sub_eq_zero]

theorem symbol_pi_neg (q : Tuning) (K : ℕ) {a b : ℝ} (ha : 0<a) (hb : 0≤b) :
    symbol q K a b frequencyPi < 0 := by
  have h1 : (tuningCurve q).lag 1 frequencyPi = -2 := by
    norm_num [Curve.lag, tuningCurve_apply, frequencyPi, Tuning.angle_pi]
  have h2 := (tuningCurve q).lag_at_pi_nonpos (-(K : ℤ))
  unfold symbol
  rw [h1]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hb h2]

end polyak.ModeLocking.TwoLag
