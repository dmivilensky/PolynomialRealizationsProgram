import nesterov.TwoStep.LagPolynomial

/-!
Article: Lemma `lem:struct`. Exact affine interpolation and the endpoint
factorizations of the finite-condition lag-one polynomial.
-/
namespace nesterov.FiniteCondition
noncomputable section
open nesterov.TwoStep Set

def tauThree (β : ℝ) : ℝ := (β^2+3*β-1)/6
def tauStar (β : ℝ) : ℝ := (β^2+4*β-1)/8
def maxStep (β τ : ℝ) : ℝ := 2*(1+β)/(1+2*τ)
def boundaryFactor (β τ ξ : ℝ) : ℝ := (1-β^2)+2*ξ*(2*τ-β)

theorem Ltau_affine_mu (β τ a b t y ξ : ℝ) :
    Ltau β τ ((1-t)*a+t*b) y ξ=
      (1-t)*Ltau β τ a y ξ+t*Ltau β τ b y ξ := by
  unfold Ltau A0 A1 A2
  ring

theorem Ltau_interpolate {β τ yμ y ξ : ℝ} (hy : y≠0) :
    Ltau β τ yμ y ξ=(1-yμ/y)*Ltau β τ 0 y ξ+(yμ/y)*Ltau β τ y y ξ := by
  convert Ltau_affine_mu β τ 0 y (yμ/y) y ξ using 1
  congr 2
  field_simp
  ring

theorem Ltau_zero_mu (β τ y ξ : ℝ) :
    Ltau β τ 0 y ξ=2*(1-β)*y+
      ξ*(2*(1-β)^2+y*(2*τ*(3-β)-2))+4*ξ^2*(β-τ*y) := by
  unfold Ltau A0 A1 A2
  ring

theorem Ltau_zero_step (β τ ξ : ℝ) :
    Ltau β τ 0 0 ξ=2*ξ*((1-β)^2+2*β*ξ) := by
  unfold Ltau A0 A1 A2
  ring

theorem Ltau_affine_step (β τ a b t ξ : ℝ) :
    Ltau β τ 0 ((1-t)*a+t*b) ξ=
      (1-t)*Ltau β τ 0 a ξ+t*Ltau β τ 0 b ξ := by
  unfold Ltau A0 A1 A2
  ring

theorem Ltau_maxStep {β τ ξ : ℝ} (hτ : 1+2*τ≠0) :
    Ltau β τ 0 (maxStep β τ) ξ=
      2*(2-ξ)/(1+2*τ)*boundaryFactor β τ ξ := by
  unfold Ltau A0 A1 A2 maxStep boundaryFactor
  field_simp
  ring

theorem boundaryFactor_zero (β τ : ℝ) : boundaryFactor β τ 0=1-β^2 := by
  simp [boundaryFactor]

theorem boundaryFactor_two (β τ : ℝ) : boundaryFactor β τ 2=8*(τ-tauStar β) := by
  unfold boundaryFactor tauStar
  ring

theorem boundaryFactor_three_halves (β τ : ℝ) :
    boundaryFactor β τ (3/2)=6*(τ-tauThree β) := by
  unfold boundaryFactor tauThree
  ring

theorem thresholds_gap (β : ℝ) : tauStar β-tauThree β=(1-β^2)/24 := by
  unfold tauStar tauThree
  ring

theorem diagonal_unit {β τ y : ℝ} {z : ℂ} (hz : Complex.normSq z=1) :
    Ltau β τ y y (1-z.re)=Complex.normSq (Quadratic.characteristic β τ 1 y z) := by
  rw [Quadratic.characteristic_eq]
  simp only [Complex.normSq_apply] at hz ⊢
  simp only [pow_two,Complex.sub_re,Complex.sub_im,
    Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im]
  unfold Ltau A0 A1 A2 Quadratic.S Quadratic.Q
  linear_combination (-(z.re^2+z.im^2)+2*(1+β-y*(1+τ))*z.re-
    (1+β-y*(1+τ))^2+2*(β-y*τ)-1)*hz

end
end nesterov.FiniteCondition
