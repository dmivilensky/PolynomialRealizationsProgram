import Mathlib.Tactic

/-!
Article: main_krylov, apG:local(b), scalar energy comparison.
Use: turn the proved small observed slope defect and the actual trial
curvature bound into a uniform lower bound on the computed block energy.
Source: elementary real inequalities; the vector inputs are instantiated
from actual normal/conjugacy solves in the neighboring local modules.
-/

namespace krylov.XR
noncomputable section

/-- A small slope defect controls the virtual gradient by the old model
energy and the actual one-dimensional trial energy, including zero slopes. -/
theorem virtual_norm_sq_from_slope (a q r z K : ℝ)
    (ha : 0 ≤ a) (hq : 0 ≤ q) (hr : 0 ≤ r) (hz : 0 ≤ z) (hK : 0 ≤ K)
    (hdefect : q ^ 2 ≤ r + a * q) (htrial : r ^ 2 ≤ K * q ^ 2 * z) :
    q ^ 2 ≤ 4 * a ^ 2 + 4 * K * z := by
  by_cases hsmall : q ≤ 2 * a
  · nlinarith [mul_nonneg hK hz]
  · have hqpos : 0 < q := by linarith
    have hrlo : q ^ 2 / 2 ≤ r := by nlinarith
    have hs := (sq_le_sq₀ (by positivity : 0 ≤ q ^ 2 / 2) hr).2 hrlo
    have hmul : q ^ 2 * q ^ 2 ≤ q ^ 2 * (4 * K * z) := by nlinarith
    have hbound := (mul_le_mul_iff_right₀ (sq_pos_of_pos hqpos)).mp hmul
    nlinarith [sq_nonneg a]

/-- One explicit uniform block-energy comparison constant. -/
def blockEnergyConstant (coercivity B K : ℝ) : ℝ :=
  max ((8 + 2 * B ^ 2) / coercivity) (8 * K)

/-- The exact computed block energy dominates the full gradient norm
with a positive constant, using only the actual slope-defect estimates. -/
theorem block_energy_controls_gradient (a q r z K B energy gradient coercivity : ℝ)
    (ha : 0 ≤ a) (hq : 0 ≤ q) (hr : 0 ≤ r) (hz : 0 ≤ z) (hK : 0 ≤ K)
    (hc : 0 < coercivity)
    (hdefect : q ^ 2 ≤ r + a * q) (htrial : r ^ 2 ≤ K * q ^ 2 * z)
    (henergy : coercivity * a ^ 2 + z ≤ energy)
    (hgradient : gradient ^ 2 ≤ 2 * q ^ 2 + 2 * B ^ 2 * a ^ 2) :
    0 < blockEnergyConstant coercivity B K ∧
      (blockEnergyConstant coercivity B K)⁻¹ * gradient ^ 2 ≤ energy := by
  have hqbound := virtual_norm_sq_from_slope a q r z K ha hq hr hz hK hdefect htrial
  have hpos : 0 < (8 + 2 * B ^ 2) / coercivity := by positivity
  have hC : 0 < blockEnergyConstant coercivity B K := hpos.trans_le (le_max_left _ _)
  have hcoef : 8 + 2 * B ^ 2 ≤ blockEnergyConstant coercivity B K * coercivity :=
    (div_le_iff₀ hc).mp (le_max_left _ _)
  have htrialcoef : 8 * K ≤ blockEnergyConstant coercivity B K := le_max_right _ _
  have hb : gradient ^ 2 ≤ blockEnergyConstant coercivity B K * energy := by
    calc
      _ ≤ (8 + 2 * B ^ 2) * a ^ 2 + 8 * K * z := by nlinarith
      _ ≤ blockEnergyConstant coercivity B K * (coercivity * a ^ 2 + z) := by
        nlinarith [mul_le_mul_of_nonneg_right hcoef (sq_nonneg a),
          mul_le_mul_of_nonneg_right htrialcoef hz]
      _ ≤ _ := mul_le_mul_of_nonneg_left henergy hC.le
  refine ⟨hC, ?_⟩
  have hd : gradient ^ 2 / blockEnergyConstant coercivity B K ≤ energy :=
    (div_le_iff₀ hC).2 (by simpa only [mul_comm] using hb)
  simpa only [div_eq_mul_inv, mul_comm] using hd

end
end krylov.XR
