import nesterov.TwoStep.LagPolynomial
import nesterov.Phase.Defect

/-! Article: Lemma E.2. The exact mixed symbol and its one-atom criterion. -/
namespace nesterov.TwoStep
noncomputable section
open Spectral Phase Set

def mixedBracket (β τ r ξ : ℝ) : ℝ :=
  (1+τ)*(r^2-β)+τ*(1+β)-2*τ*r*(1-ξ)

def mixedPolynomial (β τ yμ y r ξ : ℝ) : ℝ :=
  E0 r (Quadratic.S β τ 1 yμ) (Quadratic.S β τ 1 y)
      (Quadratic.Q β τ 1 yμ) (Quadratic.Q β τ 1 y)-
    (E1 r (Quadratic.S β τ 1 yμ) (Quadratic.S β τ 1 y) (Quadratic.Q β τ 1 y)+
      E2 r (Quadratic.S β τ 1 yμ) (Quadratic.S β τ 1 y) (Quadratic.Q β τ 1 yμ))*r*(1-ξ)+
    (Quadratic.Q β τ 1 yμ+Quadratic.Q β τ 1 y)*r^2*(1-4*ξ+2*ξ^2)+
    (2-ξ)*(y-yμ)*r*mixedBracket β τ r ξ

def mixedQ0 (β τ yμ y r : ℝ) : ℝ := mixedPolynomial β τ yμ y r 0

def mixedQ1 (β τ yμ y r : ℝ) : ℝ :=
  (E1 r (Quadratic.S β τ 1 yμ) (Quadratic.S β τ 1 y) (Quadratic.Q β τ 1 y)+
    E2 r (Quadratic.S β τ 1 yμ) (Quadratic.S β τ 1 y) (Quadratic.Q β τ 1 yμ))*r-
    4*(Quadratic.Q β τ 1 yμ+Quadratic.Q β τ 1 y)*r^2+
    (y-yμ)*r*(4*τ*r-mixedBracket β τ r 0)

def mixedQ2 (β τ yμ y r : ℝ) : ℝ :=
  2*(Quadratic.Q β τ 1 yμ+Quadratic.Q β τ 1 y)*r^2-2*τ*(y-yμ)*r^2

theorem mixedPolynomial_coefficients (β τ yμ y r ξ : ℝ) :
    mixedPolynomial β τ yμ y r ξ=mixedQ0 β τ yμ y r+
      mixedQ1 β τ yμ y r*ξ+mixedQ2 β τ yμ y r*ξ^2 := by
  unfold mixedQ0 mixedQ1 mixedQ2 mixedPolynomial mixedBracket
  ring

theorem circle_im (r ω : ℝ) : (circle r ω).im=r*Real.sin ω := by
  have hh := polyak.Waves.z_pow_im 0 ω 1
  simp only [pow_one,Nat.cast_one,one_mul,mul_zero,Real.exp_zero] at hh
  simpa [circle,Complex.mul_im] using congrArg (fun a : ℝ=>r*a) hh

theorem cross_im_circle (β τ yμ y r ω : ℝ) :
    (Quadratic.characteristic β τ 1 yμ (circle r ω)*
      star (Quadratic.characteristic β τ 1 y (circle r ω))).im=
      (y-yμ)*r*Real.sin ω*mixedBracket β τ r (1-Real.cos ω) := by
  rw [characteristic_cross_im,circle_normSq,circle_im]
  have hr : (circle r ω).re=r*Real.cos ω := by simpa using circle_pow_re r ω 1
  rw [hr]
  unfold mixedBracket
  ring

theorem mixed_symbol (β τ yμ y r ω : ℝ) :
    ((1-circle 1 ω)*Quadratic.characteristic β τ 1 yμ (circle r ω)*
      star (Quadratic.characteristic β τ 1 y (circle r ω))).re=
      (1-Real.cos ω)*mixedPolynomial β τ yμ y r (1-Real.cos ω) := by
  let B := Quadratic.characteristic β τ 1 yμ (circle r ω)*
    star (Quadratic.characteristic β τ 1 y (circle r ω))
  have hb : B.re=E0 r (Quadratic.S β τ 1 yμ) (Quadratic.S β τ 1 y)
      (Quadratic.Q β τ 1 yμ) (Quadratic.Q β τ 1 y)-
      (E1 r (Quadratic.S β τ 1 yμ) (Quadratic.S β τ 1 y) (Quadratic.Q β τ 1 y)+
        E2 r (Quadratic.S β τ 1 yμ) (Quadratic.S β τ 1 y) (Quadratic.Q β τ 1 yμ))*r*Real.cos ω+
      (Quadratic.Q β τ 1 yμ+Quadratic.Q β τ 1 y)*r^2*Real.cos (2*ω) := by
    dsimp [B]
    simp only [Quadratic.characteristic_eq]
    change (quad _ _ _*star (quad _ _ _)).re=_
    rw [quad_product (circle_normSq r ω)]
    have hs (n : ℕ) : ((star (circle r ω))^n).re=(circle r ω^n).re := by
      rw [←star_pow,Complex.star_def,Complex.conj_re]
    have hr : (circle r ω).re=r*Real.cos ω := by simpa using circle_pow_re r ω 1
    have hrs : (star (circle r ω)).re=r*Real.cos ω := by rw [Complex.star_def,Complex.conj_re,hr]
    simp only [Complex.add_re,Complex.sub_re,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,hs,circle_pow_re,hr,hrs]
    norm_num
    ring
  have hi := cross_im_circle β τ yμ y r ω
  change B.im=_ at hi
  have h1re : (circle 1 ω).re=Real.cos ω := by simpa using circle_pow_re 1 ω 1
  have h1im : (circle 1 ω).im=Real.sin ω := by simpa using circle_im 1 ω
  rw [mul_assoc]
  change ((1-circle 1 ω)*B).re=_
  rw [Complex.mul_re,Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,h1re,h1im,hb,hi,
    Real.cos_two_mul]
  unfold mixedPolynomial
  have hsin := Real.sin_sq_add_cos_sq ω
  linear_combination (y-yμ)*r*mixedBracket β τ r (1-Real.cos ω)*hsin

end
end nesterov.TwoStep
