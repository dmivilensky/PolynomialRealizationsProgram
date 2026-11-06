import nesterov.TwoStep.Symbol

/-! Article: Lemma E.1, all four exact coefficients in ξ=1−cos ω. -/
namespace nesterov.TwoStep
noncomputable section

def P0 (r Sμ SL Qμ QL : ℝ) : ℝ := (1-r)*(r^2-Sμ*r+Qμ)*(r^2-SL*r+QL)
def P1 (r Sμ SL Qμ QL : ℝ) : ℝ :=
  r*(E0 r Sμ SL Qμ QL+E1 r Sμ SL QL+E2 r Sμ SL Qμ+Qμ*r^2)-
    4*r^2*(E1 r Sμ SL QL+Qμ+QL)+9*QL*r^3
def P2 (r Sμ SL Qμ QL : ℝ) : ℝ := 2*r^2*(E1 r Sμ SL QL+Qμ+QL)-12*QL*r^3
def P3 (r QL : ℝ) : ℝ := 4*QL*r^3

theorem lagOne_cubic (r ω Sμ SL Qμ QL : ℝ) :
    ((1-circle r ω)*quad Sμ Qμ (circle r ω)*star (quad SL QL (circle r ω))).re=
      P0 r Sμ SL Qμ QL+P1 r Sμ SL Qμ QL*(1-Real.cos ω)+
        P2 r Sμ SL Qμ QL*(1-Real.cos ω)^2+P3 r QL*(1-Real.cos ω)^3 := by
  rw [lagOne_trigonometric,Real.cos_two_mul,Real.cos_three_mul]
  unfold P0 P1 P2 P3 E0 E1 E2
  ring

theorem lagOne_at_pi (r Sμ SL Qμ QL : ℝ) :
    ((1-circle r Real.pi)*quad Sμ Qμ (circle r Real.pi)*star (quad SL QL (circle r Real.pi))).re=
      (1+r)*(r^2+Sμ*r+Qμ)*(r^2+SL*r+QL) := by
  rw [lagOne_cubic,Real.cos_pi]
  unfold P0 P1 P2 P3 E0 E1 E2
  ring

theorem lagOne_at_zero (r Sμ SL Qμ QL : ℝ) :
    ((1-circle r 0)*quad Sμ Qμ (circle r 0)*star (quad SL QL (circle r 0))).re=P0 r Sμ SL Qμ QL := by
  rw [lagOne_cubic,Real.cos_zero]
  ring

end
end nesterov.TwoStep
