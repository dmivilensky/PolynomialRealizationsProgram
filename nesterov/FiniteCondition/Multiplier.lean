import nesterov.FiniteCondition.Structure

/-! The literal upper-lag-two polynomial of the tongue-free certificate. -/
namespace nesterov.FiniteCondition
noncomputable section
open nesterov.TwoStep Set

def skewPolynomial (β τ yμ y ξ : ℝ) : ℝ := (y-yμ)*((1-β)+2*τ*ξ)
def mixedPolynomial (β τ lam yμ y ξ : ℝ) : ℝ :=
  (1+2*lam*(2-ξ))*Ltau β τ yμ y ξ+
    2*lam*(2-ξ)*(2*ξ-3)*skewPolynomial β τ yμ y ξ

def multiplierDenominator (β τ : ℝ) : ℝ := 1+2*β-β^2+2*τ*(1+3*β)
def lagTwoWeight (β τ : ℝ) : ℝ := (β-2*τ)/multiplierDenominator β τ

theorem mixed_affine_mu (β τ lam a b t y ξ : ℝ) :
    mixedPolynomial β τ lam ((1-t)*a+t*b) y ξ=
      (1-t)*mixedPolynomial β τ lam a y ξ+t*mixedPolynomial β τ lam b y ξ := by
  unfold mixedPolynomial skewPolynomial Ltau A0 A1 A2
  ring

theorem mixed_affine_step (β τ lam a b t ξ : ℝ) :
    mixedPolynomial β τ lam 0 ((1-t)*a+t*b) ξ=
      (1-t)*mixedPolynomial β τ lam 0 a ξ+t*mixedPolynomial β τ lam 0 b ξ := by
  unfold mixedPolynomial skewPolynomial Ltau A0 A1 A2
  ring

theorem mixed_diagonal (β τ lam y ξ : ℝ) :
    mixedPolynomial β τ lam y y ξ=(1+2*lam*(2-ξ))*Ltau β τ y y ξ := by
  simp [mixedPolynomial,skewPolynomial]

theorem mixed_zero_step (β τ lam ξ : ℝ) :
    mixedPolynomial β τ lam 0 0 ξ=(1+2*lam*(2-ξ))*Ltau β τ 0 0 ξ := by
  simp [mixedPolynomial,skewPolynomial]

theorem mixed_maxStep {β τ lam ξ : ℝ} (hτ : 1+2*τ≠0) :
    mixedPolynomial β τ lam 0 (maxStep β τ) ξ=
      2*(2-ξ)/(1+2*τ)*((1+2*lam*(2-ξ))*boundaryFactor β τ ξ+
        2*lam*(2*ξ-3)*(1+β)*((1-β)+2*τ*ξ)) := by
  rw [mixedPolynomial,Ltau_maxStep hτ]
  unfold skewPolynomial maxStep
  field_simp
  ring

theorem multiplier_square {β τ ξ : ℝ} (hd : multiplierDenominator β τ≠0) :
    (1+2*lagTwoWeight β τ*(2-ξ))*boundaryFactor β τ ξ+
        2*lagTwoWeight β τ*(2*ξ-3)*(1+β)*((1-β)+2*τ*ξ)=
      6*(1+lagTwoWeight β τ)*(τ-tauThree β)+
        4*lagTwoWeight β τ*β*(1+2*τ)*(ξ-3/2)^2 := by
  unfold lagTwoWeight boundaryFactor tauThree
  field_simp
  unfold multiplierDenominator
  ring

theorem cross_re_unit {β τ yμ y : ℝ} {z : ℂ} (hz : Complex.normSq z=1) :
    (Quadratic.characteristic β τ 1 yμ z*star (Quadratic.characteristic β τ 1 y z)).re=
      Ltau β τ yμ y (1-z.re)-(1+z.re)*skewPolynomial β τ yμ y (1-z.re) := by
  rw [Quadratic.characteristic_eq,Quadratic.characteristic_eq]
  simp only [Complex.normSq_apply] at hz
  simp only [pow_two,Complex.star_def,Complex.mul_re,Complex.mul_im,
    Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.conj_re,Complex.conj_im]
  unfold Ltau A0 A1 A2 skewPolynomial Quadratic.S Quadratic.Q
  linear_combination (z.re^2+z.im^2+1-
    ((1+β-1*yμ*(1+τ))+(1+β-1*y*(1+τ)))*z.re+
    (1+β-1*yμ*(1+τ))*(1+β-1*y*(1+τ))-
    ((β-1*yμ*τ)+(β-1*y*τ)))*hz

theorem mixed_unit {β τ lam yμ y : ℝ} {z : ℂ} (hz : Complex.normSq z=1) :
    (Quadratic.characteristic β τ 1 yμ z*star (Quadratic.characteristic β τ 1 y z)*
      ((1-z)+(lam:ℂ)*(1-star z^2))).re=
      (1-z.re)*mixedPolynomial β τ lam yμ y (1-z.re) := by
  have hr := cross_re_unit (β:=β) (τ:=τ) (yμ:=yμ) (y:=y) hz
  have hi := Phase.characteristic_cross_im_unit β τ 1 yμ y hz
  simp only [one_mul] at hi
  simp only [Complex.normSq_apply] at hz
  rw [Complex.mul_re,hr,hi]
  simp only [Complex.mul_re,Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
    Complex.one_re,Complex.one_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.star_def,Complex.conj_re,Complex.conj_im,pow_two,Complex.mul_im]
  unfold mixedPolynomial skewPolynomial
  linear_combination (lam*(Ltau β τ yμ y (1-z.re)-
    (1+z.re)*((y-yμ)*((1-β)+2*τ*(1-z.re))))+
      ((y-yμ)*((1-β)+2*τ*(1-z.re)))*(1-2*lam*z.re))*hz

end
end nesterov.FiniteCondition
