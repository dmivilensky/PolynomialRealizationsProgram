import polyak.Dynamics.Tuning
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
Article: the exact threshold κ_c=9+4√5=φ⁶ and q_c=φ⁻¹.
Use: compare the original condition number with the spectral threshold without approximations.
Proof: the golden-ratio quadratic and positive square-root identities.
-/

noncomputable section

open scoped goldenRatio

namespace polyak.Threshold

/-- Article: the critical condition number. -/
def criticalKappa : ℝ := 9+4*Real.sqrt 5

/-- Article: the critical quadratic factor. -/
def criticalQ : ℝ := φ⁻¹

/-- Article: the golden-ratio inverse in polynomial form. -/
theorem criticalQ_eq : criticalQ = φ-1 := by
  unfold criticalQ
  apply inv_eq_of_mul_eq_one_left
  nlinarith [Real.goldenRatio_sq]

/-- Article: q_c lies in the actual open tuning interval. -/
theorem criticalQ_pos : 0 < criticalQ := inv_pos.mpr Real.goldenRatio_pos

/-- Article: q_c lies in the actual open tuning interval. -/
theorem criticalQ_lt_one : criticalQ < 1 := by
  rw [criticalQ_eq]
  linarith [Real.goldenRatio_lt_two]

/-- Article: q_c is the positive zero of 1-q-q². -/
theorem criticalQ_sq_add : criticalQ^2+criticalQ = 1 := by
  rw [criticalQ_eq]
  nlinarith [Real.goldenRatio_sq]

/-- Article: the square root of κ_c is φ³=2φ+1. -/
theorem criticalKappa_sq : criticalKappa = (2*φ+1)^2 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  unfold criticalKappa
  dsimp [Real.goldenRatio]
  nlinarith [hs]

/-- Article: the exact printed power identity κ_c=φ⁶. -/
theorem criticalKappa_eq_golden_pow : criticalKappa = φ^6 := by
  rw [criticalKappa_sq]
  have h₃ : φ^3 = 2*φ+1 := by nlinarith [Real.goldenRatio_sq]
  rw [show (6 : ℕ) = 3*2 by rfl, pow_mul, h₃]

/-- Article: κ_c>1. -/
theorem one_lt_criticalKappa : 1 < criticalKappa := by
  unfold criticalKappa
  nlinarith [Real.sqrt_nonneg 5]

/-- Article: exact square root of the critical condition number. -/
theorem sqrt_criticalKappa : Real.sqrt criticalKappa = 2*φ+1 := by
  rw [criticalKappa_sq, Real.sqrt_sq (by linarith [Real.goldenRatio_pos] : 0 ≤ 2*φ+1)]

/-- Article: the condition-number factor lies in (0,1). -/
theorem conditionQ_mem {κ : ℝ} (hκ : 1 < κ) :
    0 < Dynamics.conditionQ κ ∧ Dynamics.conditionQ κ < 1 := by
  have hs : 1 < Real.sqrt κ := by
    simpa using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hκ
  unfold Dynamics.conditionQ
  constructor
  · exact div_pos (by linarith) (by linarith)
  · exact (div_lt_one (by linarith : 0 < Real.sqrt κ+1)).mpr (by linarith)

/-- Article: q<q_c is precisely κ<κ_c. -/
theorem conditionQ_lt_critical_iff {κ : ℝ} (hκ : 1 < κ) :
    Dynamics.conditionQ κ < criticalQ ↔ κ < criticalKappa := by
  have hs : 1 < Real.sqrt κ := by
    simpa using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hκ
  have hp : 0 < 2-φ := by linarith [Real.goldenRatio_lt_two]
  have hsκ := Real.sq_sqrt (show 0 ≤ κ by linarith)
  have hpoly : (2-φ)*(2*φ+1) = φ := by nlinarith [Real.goldenRatio_sq]
  rw [Dynamics.conditionQ, criticalQ_eq, div_lt_iff₀ (by linarith : 0 < Real.sqrt κ+1)]
  rw [criticalKappa_sq]
  constructor
  · intro hh
    have ht : Real.sqrt κ < 2*φ+1 := by
      apply (mul_lt_mul_iff_right₀ hp).mp
      nlinarith [hpoly]
    nlinarith [sq_nonneg (Real.sqrt κ-(2*φ+1)), Real.goldenRatio_pos]
  · intro hh
    have ht : Real.sqrt κ < 2*φ+1 := by nlinarith [Real.goldenRatio_pos]
    have hm := mul_lt_mul_of_pos_left ht hp
    nlinarith [hpoly]

/-- Article: q=q_c is precisely κ=κ_c. -/
theorem conditionQ_eq_critical_iff {κ : ℝ} (hκ : 1 < κ) :
    Dynamics.conditionQ κ = criticalQ ↔ κ = criticalKappa := by
  have hs : 1 < Real.sqrt κ := by
    simpa using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hκ
  have hp : 0 < 2-φ := by linarith [Real.goldenRatio_lt_two]
  have hsκ := Real.sq_sqrt (show 0 ≤ κ by linarith)
  have hpoly : (2-φ)*(2*φ+1) = φ := by nlinarith [Real.goldenRatio_sq]
  rw [Dynamics.conditionQ, criticalQ_eq, div_eq_iff (by linarith : Real.sqrt κ+1 ≠ 0)]
  constructor
  · intro hh
    have ht : Real.sqrt κ = 2*φ+1 := by nlinarith [hpoly]
    rw [criticalKappa_sq]
    nlinarith [hsκ]
  · intro hh
    have ht : Real.sqrt κ = 2*φ+1 := by rw [hh,sqrt_criticalKappa]
    rw [ht]
    nlinarith [Real.goldenRatio_sq]

/-- Article: q>q_c is precisely κ>κ_c. -/
theorem critical_lt_conditionQ_iff {κ : ℝ} (hκ : 1 < κ) :
    criticalQ < Dynamics.conditionQ κ ↔ criticalKappa < κ := by
  rw [← not_le, le_iff_lt_or_eq, conditionQ_lt_critical_iff hκ,
    conditionQ_eq_critical_iff hκ, ← le_iff_lt_or_eq, not_le]

end polyak.Threshold
