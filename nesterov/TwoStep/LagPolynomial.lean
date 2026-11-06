import nesterov.TwoStep.Cubic
import nesterov.Momentum.Parameters

/-!
Article: Proposition 6.1(a), Equation (Acoef), and the exact limit polynomial.
All identities are polynomial identities, before any stability assumption.
-/
namespace nesterov.TwoStep
noncomputable section

def A0 (β yμ y : ℝ) : ℝ := 2*(1-β)*(y-yμ)+yμ*y
def A1 (β τ yμ y : ℝ) : ℝ := 2*(1-β)^2-2*yμ*(β+β*τ+τ)+
  y*(6*τ-2-2*β*τ)+2*τ*(1+τ)*yμ*y
def A2 (β τ y : ℝ) : ℝ := 4*(β-τ*y)
def Ltau (β τ yμ y ξ : ℝ) : ℝ := A0 β yμ y+A1 β τ yμ y*ξ+A2 β τ y*ξ^2

theorem characteristic_unit_step (β τ h lam : ℝ) (z : ℂ) :
    Quadratic.characteristic β τ h lam z=Quadratic.characteristic β τ 1 (h*lam) z := by
  unfold Quadratic.characteristic
  push_cast
  ring

theorem lagOne_polynomial (β τ yμ y ω : ℝ) :
    ((1-circle 1 ω)*Quadratic.characteristic β τ 1 yμ (circle 1 ω)*
      star (Quadratic.characteristic β τ 1 y (circle 1 ω))).re=
      (1-Real.cos ω)*Ltau β τ yμ y (1-Real.cos ω) := by
  simp only [Quadratic.characteristic_eq]
  change ((1-circle 1 ω)*quad (Quadratic.S β τ 1 yμ) (Quadratic.Q β τ 1 yμ) (circle 1 ω)*
    star (quad (Quadratic.S β τ 1 y) (Quadratic.Q β τ 1 y) (circle 1 ω))).re=_
  rw [lagOne_cubic]
  unfold P0 P1 P2 P3 E0 E1 E2 Ltau A0 A1 A2 Quadratic.S Quadratic.Q
  ring

theorem physical_lagOne_polynomial (β τ h μ L ω : ℝ) :
    ((1-circle 1 ω)*Quadratic.characteristic β τ h μ (circle 1 ω)*
      star (Quadratic.characteristic β τ h L (circle 1 ω))).re=
      (1-Real.cos ω)*Ltau β τ (h*μ) (h*L) (1-Real.cos ω) := by
  rw [characteristic_unit_step β τ h μ,characteristic_unit_step β τ h L]
  exact lagOne_polynomial β τ (h*μ) (h*L) ω

@[simp] theorem Ltau_zero (β τ yμ y : ℝ) : Ltau β τ yμ y 0=A0 β yμ y := by simp [Ltau]

theorem Ltau_two (β τ yμ y : ℝ) :
    Ltau β τ yμ y 2=(2*(1+β)-yμ*(1+2*τ))*(2*(1+β)-y*(1+2*τ)) := by
  unfold Ltau A0 A1 A2
  ring

theorem Ltau_limit (τ y ξ : ℝ) :
    Ltau 1 τ 0 y ξ=2*y*(2*τ-1)*ξ+4*(1-τ*y)*ξ^2 := by
  unfold Ltau A0 A1 A2
  ring

theorem Ltau_zero_pos {β τ yμ y : ℝ} (hβ : β<1) (hμ : 0<yμ) (hy : yμ<y) :
    0<Ltau β τ yμ y 0 := by
  rw [Ltau_zero]
  unfold A0
  have h₁ := mul_pos (mul_pos (by norm_num : (0:ℝ)<2) (sub_pos.mpr hβ)) (sub_pos.mpr hy)
  have h₂ := mul_pos hμ (hμ.trans hy)
  linarith

theorem stable_Ltau_two_pos (q : Momentum.Tuning) {μ L : ℝ}
    (hμ : 0<μ) (hμL : μ<L) (hs : q.Stable μ L) :
    0<Ltau q.beta q.tau (q.stepSize*μ) (q.stepSize*L) 2 := by
  rw [Ltau_two]
  have hh := (q.stable_iff hμ hμL).mp hs
  have hlo : q.stepSize*μ*(1+2*q.tau)<q.stepSize*L*(1+2*q.tau) :=
    mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hμL q.step_pos) (by linarith [q.tau_nonneg])
  exact mul_pos (by linarith) (by linarith)

end
end nesterov.TwoStep
