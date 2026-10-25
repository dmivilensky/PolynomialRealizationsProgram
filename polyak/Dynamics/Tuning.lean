import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
Article: polyaksiopt, introduction eq:polyak and Lemma normalization.
Use: exact real parameter domains and Polyak's normalized coefficients.
-/

namespace polyak.Dynamics
noncomputable section

/-- Article: eq:polyak. Use: Polyak step size in the original curvature units. -/
def polyakAlpha (μ L : ℝ) : ℝ := 4 / (Real.sqrt L + Real.sqrt μ)^2

/-- Article: eq:polyak. Use: the quadratic rate factor in curvature units. -/
def polyakQ (μ L : ℝ) : ℝ :=
  (Real.sqrt L - Real.sqrt μ) / (Real.sqrt L + Real.sqrt μ)

/-- Article: eq:polyak. Use: the momentum in the actual executor. -/
def polyakBeta (μ L : ℝ) : ℝ := polyakQ μ L ^ 2

/-- Article: eq:polyak. Use: the condition-number expression printed in the source. -/
def conditionQ (κ : ℝ) : ℝ := (Real.sqrt κ - 1) / (Real.sqrt κ + 1)

/-- Article: eq:normrec. Use: the coefficient of the normalized position. -/
def normalizedA (μ L α β : ℝ) : ℝ := 1 + β - α * (L+μ) / 2

/-- Article: eq:normrec. Use: the coefficient of the normalized gradient. -/
def normalizedB (μ L α : ℝ) : ℝ := α * (L-μ) / 2

/-- Article: eq:polyak. Use: all denominator manipulations have a positive scale. -/
theorem sqrt_sum_pos {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L) :
    0 < Real.sqrt L + Real.sqrt μ :=
  add_pos (Real.sqrt_pos.2 (hμ.trans hL)) (Real.sqrt_pos.2 hμ)

/-- Article: eq:polyak. Use: the factor lies in its original open domain. -/
theorem polyakQ_pos {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L) : 0 < polyakQ μ L := by
  exact div_pos (sub_pos.2 (Real.sqrt_lt_sqrt hμ.le hL)) (sqrt_sum_pos hμ hL)

/-- Article: eq:polyak. Use: convergence of the auxiliary quadratic coordinates. -/
theorem polyakQ_lt_one {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L) : polyakQ μ L < 1 := by
  apply (div_lt_one (sqrt_sum_pos hμ hL)).2
  have := Real.sqrt_pos.2 hμ
  linarith

/-- Article: eq:polyak. Use: the actual step size is positive. -/
theorem polyakAlpha_pos {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L) :
    0 < polyakAlpha μ L := by
  exact div_pos (by norm_num) (sq_pos_of_pos (sqrt_sum_pos hμ hL))

/-- Article: eq:polyak. Use: the original momentum belongs to [0,1). -/
theorem polyakBeta_mem {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L) :
    0 ≤ polyakBeta μ L ∧ polyakBeta μ L < 1 := by
  have hq := polyakQ_pos hμ hL
  have hq1 := polyakQ_lt_one hμ hL
  dsimp [polyakBeta]
  constructor
  · positivity
  · nlinarith

/-- Article: eq:polyak. Use: curvature and condition-number definitions coincide.
Proof: multiply numerator and denominator by the positive square root of μ. -/
theorem polyakQ_eq_conditionQ {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L) :
    polyakQ μ L = conditionQ (L/μ) := by
  have hsμ : Real.sqrt μ ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hμ)
  have hs : Real.sqrt L + Real.sqrt μ ≠ 0 := ne_of_gt (sqrt_sum_pos hμ hL)
  rw [conditionQ, Real.sqrt_div (hμ.trans hL).le]
  dsimp [polyakQ]
  field_simp

/-- Article: lem:normalization. Use: the position term vanishes under Polyak tuning. -/
theorem polyak_normalizedA {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L) :
    normalizedA μ L (polyakAlpha μ L) (polyakBeta μ L) = 0 := by
  have hs := ne_of_gt (sqrt_sum_pos hμ hL)
  have hm := Real.sq_sqrt hμ.le
  have hl := Real.sq_sqrt (hμ.trans hL).le
  unfold normalizedA polyakAlpha polyakBeta polyakQ
  field_simp
  nlinarith

/-- Article: lem:normalization. Use: the normalized forcing is exactly 2q. -/
theorem polyak_normalizedB {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L) :
    normalizedB μ L (polyakAlpha μ L) = 2 * polyakQ μ L := by
  have hs := ne_of_gt (sqrt_sum_pos hμ hL)
  have hm := Real.sq_sqrt hμ.le
  have hl := Real.sq_sqrt (hμ.trans hL).le
  unfold normalizedB polyakAlpha polyakQ
  field_simp
  nlinarith

/-- Article: eq:quad. Use: the prescribed parameters satisfy quadratic stability. -/
theorem polyak_quadratic_condition {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L) :
    0 < polyakAlpha μ L * L ∧
      polyakAlpha μ L * L < 2 * (1 + polyakBeta μ L) := by
  have ha := polyakAlpha_pos hμ hL
  have hq := polyakQ_pos hμ hL
  have hq1 := polyakQ_lt_one hμ hL
  have hA := polyak_normalizedA hμ hL
  have hB := polyak_normalizedB hμ hL
  dsimp [normalizedA] at hA
  dsimp [normalizedB] at hB
  constructor
  · exact mul_pos ha (hμ.trans hL)
  · have hb : polyakBeta μ L = polyakQ μ L ^ 2 := rfl
    nlinarith [sq_pos_of_pos (sub_pos.2 hq1)]

end
end polyak.Dynamics
