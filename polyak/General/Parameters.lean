import polyak.Dynamics.QuadraticRate
import polyak.Waves.Complex
import polyak.Dynamics.Rate

/-! Article: Part II eq:ab, eq:quad, and Appendix D.
Admissible tunings in the source coordinates, with exact original-unit bridges. -/

namespace polyak.General
noncomputable section

/-- A tuning in the relative open domain used throughout Part II. -/
structure Tuning where
  kappa : ℝ
  y : ℝ
  beta : ℝ
  kappa_gt_one : 1 < kappa
  beta_nonneg : 0 ≤ beta
  beta_lt_one : beta < 1
  y_pos : 0 < y
  y_lt : y < 2 * (1 + beta)

namespace Tuning

def x (q : Tuning) : ℝ := q.y / q.kappa
def A (q : Tuning) : ℝ := 1 + q.beta - (q.x + q.y) / 2
def B (q : Tuning) : ℝ := (q.y - q.x) / 2
def a (q : Tuning) (z : ℂ) : ℂ := z^2 - (1 + q.beta - q.x : ℝ) * z + q.beta
def b (q : Tuning) (z : ℂ) : ℂ := z^2 - (1 + q.beta - q.y : ℝ) * z + q.beta
def rate (q : Tuning) : ℝ := Dynamics.rate q.x q.y 1 q.beta

theorem normalizedA_eq (q : Tuning) : Dynamics.normalizedA q.x q.y 1 q.beta=q.A := by
  dsimp [Dynamics.normalizedA,A]; ring
theorem normalizedB_eq (q : Tuning) : Dynamics.normalizedB q.x q.y 1=q.B := by
  dsimp [Dynamics.normalizedB,B]; ring

theorem kappa_pos (q : Tuning) : 0 < q.kappa := lt_trans zero_lt_one q.kappa_gt_one
theorem x_pos (q : Tuning) : 0 < q.x := div_pos q.y_pos q.kappa_pos
theorem x_lt_y (q : Tuning) : q.x < q.y := by
  dsimp [x]
  exact (div_lt_iff₀ q.kappa_pos).2 (by nlinarith [q.y_pos, q.kappa_gt_one])
theorem B_pos (q : Tuning) : 0 < q.B := by dsimp [B]; linarith [q.x_lt_y]
theorem B_ne_zero (q : Tuning) : q.B ≠ 0 := ne_of_gt q.B_pos
theorem A_add_B (q : Tuning) : q.A + q.B = 1 + q.beta - q.x := by dsimp [A,B]; ring
theorem A_sub_B (q : Tuning) : q.A - q.B = 1 + q.beta - q.y := by dsimp [A,B]; ring
theorem two_B (q : Tuning) : 2 * q.B = q.y - q.x := by dsimp [B]; ring
theorem abs_A_add_B_lt (q : Tuning) : |q.A| + q.B < 1 + q.beta := by
  by_cases h : 0 ≤ q.A
  · rw [abs_of_nonneg h, q.A_add_B]; linarith [q.x_pos]
  · rw [abs_of_neg (lt_of_not_ge h)]
    have := q.A_sub_B
    linarith [q.y_lt]

theorem a_sub_b (q : Tuning) (z : ℂ) : q.a z - q.b z = (q.x - q.y : ℝ) * z := by
  simp only [a,b, Complex.ofReal_sub]; ring
@[simp] theorem a_one (q : Tuning) : q.a 1 = (q.x : ℂ) := by
  simp only [a, one_pow, mul_one, Complex.ofReal_sub, Complex.ofReal_add,
    Complex.ofReal_one]; ring
@[simp] theorem b_one (q : Tuning) : q.b 1 = (q.y : ℂ) := by
  simp only [b, one_pow, mul_one, Complex.ofReal_sub, Complex.ofReal_add,
    Complex.ofReal_one]; ring

theorem a_root_stable (q : Tuning) {z : ℂ} (hz : q.a z = 0) : ‖z‖ < 1 := by
  apply Dynamics.quadratic_root_norm_lt_one q.beta_nonneg q.beta_lt_one _ hz
  rw [abs_lt]; constructor <;> linarith [q.x_pos, q.x_lt_y, q.y_lt]
theorem b_root_stable (q : Tuning) {z : ℂ} (hz : q.b z = 0) : ‖z‖ < 1 := by
  apply Dynamics.quadratic_root_norm_lt_one q.beta_nonneg q.beta_lt_one _ hz
  rw [abs_lt]; constructor <;> linarith [q.y_pos, q.y_lt]
theorem a_ne_zero_of_one_le_norm (q : Tuning) {z : ℂ} (hz : 1 ≤ ‖z‖) : q.a z ≠ 0 :=
  fun h => (q.a_root_stable h).not_ge hz
theorem b_ne_zero_of_one_le_norm (q : Tuning) {z : ℂ} (hz : 1 ≤ ‖z‖) : q.b z ≠ 0 :=
  fun h => (q.b_root_stable h).not_ge hz

/-- Every admissible original-unit tuning supplies the source coordinates. -/
def ofOriginal (μ L α β : ℝ) (hμ : 0 < μ) (hL : μ < L) (hα : 0 < α)
    (hβ : 0 ≤ β) (hβ1 : β < 1) (hquad : α*L < 2*(1+β)) : Tuning where
  kappa := L / μ
  y := α * L
  beta := β
  kappa_gt_one := (one_lt_div hμ).2 hL
  beta_nonneg := hβ
  beta_lt_one := hβ1
  y_pos := mul_pos hα (hμ.trans hL)
  y_lt := hquad

theorem ofOriginal_x (μ L α β : ℝ) (hμ : 0 < μ) (hL : μ < L) (hα : 0 < α)
    (hβ : 0 ≤ β) (hβ1 : β < 1) (hquad : α*L < 2*(1+β)) :
    (ofOriginal μ L α β hμ hL hα hβ hβ1 hquad).x = α * μ := by
  dsimp [ofOriginal, x]
  field_simp [ne_of_gt (hμ.trans hL)]

end Tuning
end
end polyak.General
