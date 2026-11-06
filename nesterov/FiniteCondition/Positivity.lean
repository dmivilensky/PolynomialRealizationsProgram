import nesterov.FiniteCondition.Multiplier

/-! Strict positivity in the entire stable range, with the source's exact weights. -/
namespace nesterov.FiniteCondition
noncomputable section
open nesterov.TwoStep Set

private theorem affine_pos {a b t : ℝ} (ha : 0<a) (hb : 0≤b) (ht : 0≤t) (ht1 : t<1) :
    0<(1-t)*a+t*b :=
  add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr ht1) ha) (mul_nonneg ht hb)

theorem maxStep_pos {β τ : ℝ} (hβ : 0≤β) (hτ : 0≤τ) : 0<maxStep β τ := by
  unfold maxStep
  positivity

theorem zero_step_pos {β τ ξ : ℝ} (hβ : 0≤β) (hβ1 : β<1) (hξ : 0<ξ) :
    0<Ltau β τ 0 0 ξ := by
  rw [Ltau_zero_step]
  exact mul_pos (by positivity) (add_pos_of_pos_of_nonneg
    (sq_pos_of_pos (sub_pos.mpr hβ1)) (by positivity))

theorem boundaryFactor_nonneg {β τ ξ : ℝ} (hβ : 0≤β) (hβ1 : β<1)
    (ht : tauStar β≤τ) (hξ0 : 0≤ξ) (hξ2 : ξ≤2) : 0≤boundaryFactor β τ ξ := by
  have hb0 : 0≤1-β^2 := by nlinarith
  have hb2 : 0≤boundaryFactor β τ 2 := by rw [boundaryFactor_two];positivity
  have he : boundaryFactor β τ ξ=(1-ξ/2)*(1-β^2)+(ξ/2)*boundaryFactor β τ 2 := by
    unfold boundaryFactor
    ring
  rw [he]
  exact add_nonneg (mul_nonneg (by linarith) hb0) (mul_nonneg (by positivity) hb2)

theorem lagOne_zero_mu_pos {β τ y ξ : ℝ} (hβ : 0≤β) (hβ1 : β<1) (hτ : 0≤τ)
    (ht : tauStar β≤τ) (hy : 0≤y) (hym : y<maxStep β τ) (hξ : ξ∈Ioc (0:ℝ) 2) :
    0<Ltau β τ 0 y ξ := by
  have hm := maxStep_pos hβ hτ
  have ht0 : 0≤y/maxStep β τ := div_nonneg hy hm.le
  have ht1 : y/maxStep β τ<1 := (div_lt_one hm).mpr hym
  have hmax : 0≤Ltau β τ 0 (maxStep β τ) ξ := by
    rw [Ltau_maxStep (by positivity : 1+2*τ≠0)]
    exact mul_nonneg (div_nonneg (by linarith [hξ.2]) (by positivity))
      (boundaryFactor_nonneg hβ hβ1 ht hξ.1.le hξ.2)
  have hh := affine_pos (zero_step_pos (τ:=τ) hβ hβ1 hξ.1) hmax ht0 ht1
  rw [←Ltau_affine_step] at hh
  simpa only [mul_zero,zero_add,div_mul_cancel₀ _ hm.ne'] using hh

theorem diagonal_pos_of_nonzero {β τ y ξ : ℝ} (hξ : ξ∈Icc (0:ℝ) 2)
    (hno : ∀ z : ℂ,Complex.normSq z=1 → Quadratic.characteristic β τ 1 y z≠0) :
    0<Ltau β τ y y ξ := by
  let z : ℂ := ⟨1-ξ,Real.sqrt (ξ*(2-ξ))⟩
  have hs : (Real.sqrt (ξ*(2-ξ)))^2=ξ*(2-ξ) :=
    Real.sq_sqrt (mul_nonneg hξ.1 (by linarith [hξ.2]))
  have hz : Complex.normSq z=1 := by
    change (1-ξ)*(1-ξ)+Real.sqrt (ξ*(2-ξ))*Real.sqrt (ξ*(2-ξ))=1
    nlinarith
  have he : 1-z.re=ξ := by dsimp [z];ring
  rw [←he,diagonal_unit hz]
  exact Complex.normSq_pos.mpr (hno z hz)

theorem diagonal_nonzero_of_margin {β τ y : ℝ} (hβ : 0≤β) (hβ1 : β<1)
    (hτ : 0≤τ) (hy : 0<y) (hym : y<maxStep β τ) :
    ∀ z : ℂ,Complex.normSq z=1 → Quadratic.characteristic β τ 1 y z≠0 := by
  have hmargin : 1*y*(1+2*τ)<2*(1+β) := by
    have hh := (lt_div_iff₀ (show 0<1+2*τ by positivity)).mp hym
    simpa only [one_mul] using hh
  have hs := (Quadratic.stable_iff (μ:=y/2) (L:=y) (β:=β) (τ:=τ) (h:=1)
    (by linarith) (by linarith) (by norm_num) hβ hβ1 hτ).mpr hmargin
  intro z hz he
  have hh := hs y ⟨by linarith,le_rfl⟩ z he
  have hn : ‖z‖=1 := by
    have hh := Complex.normSq_eq_norm_sq z
    nlinarith [norm_nonneg z]
  linarith

theorem lagOne_pos {β τ yμ y ξ : ℝ} (hβ : 0≤β) (hβ1 : β<1) (hτ : 0≤τ)
    (ht : tauStar β≤τ) (hμ : 0<yμ) (hy : yμ<y) (hym : y<maxStep β τ)
    (hξ : ξ∈Ioc (0:ℝ) 2) : 0<Ltau β τ yμ y ξ := by
  have hy0 := hμ.trans hy
  rw [Ltau_interpolate hy0.ne']
  exact affine_pos (lagOne_zero_mu_pos hβ hβ1 hτ ht hy0.le hym hξ)
    (diagonal_pos_of_nonzero ⟨hξ.1.le,hξ.2⟩
      (diagonal_nonzero_of_margin hβ hβ1 hτ hy0 hym)).le
    (div_nonneg hμ.le hy0.le) ((div_lt_one hy0).mpr hy)

theorem multiplierDenominator_pos {β τ : ℝ} (hβ : 0≤β) (hβ1 : β<1) (hτ : 0≤τ) :
    0<multiplierDenominator β τ := by
  have hb : 0<1-β^2 := by nlinarith
  have hh : 0≤2*τ*(1+3*β) := by positivity
  unfold multiplierDenominator
  linarith

theorem lagTwoWeight_pos {β τ : ℝ} (hβ : 0≤β) (hβ1 : β<1) (hτ : 0≤τ)
    (ht : τ<tauStar β) : 0<lagTwoWeight β τ := by
  have hb : 0<β-2*τ := by dsimp [tauStar] at ht;nlinarith
  exact div_pos hb (multiplierDenominator_pos hβ hβ1 hτ)

theorem mixed_zero_mu_pos {β τ y ξ : ℝ} (hβ : 0≤β) (hβ1 : β<1) (hτ : 0≤τ)
    (ht3 : tauThree β≤τ) (hts : τ<tauStar β) (hy : 0≤y)
    (hym : y<maxStep β τ) (hξ : ξ∈Ioc (0:ℝ) 2) :
    0<mixedPolynomial β τ (lagTwoWeight β τ) 0 y ξ := by
  have hm := maxStep_pos hβ hτ
  have hl := lagTwoWeight_pos hβ hβ1 hτ hts
  have hm0 : 0<mixedPolynomial β τ (lagTwoWeight β τ) 0 0 ξ := by
    rw [mixed_zero_step]
    exact mul_pos (by nlinarith [mul_nonneg hl.le (sub_nonneg.mpr hξ.2)])
      (zero_step_pos hβ hβ1 hξ.1)
  have hmax : 0≤mixedPolynomial β τ (lagTwoWeight β τ) 0 (maxStep β τ) ξ := by
    rw [mixed_maxStep (by positivity : 1+2*τ≠0),
      multiplier_square (multiplierDenominator_pos hβ hβ1 hτ).ne']
    have hthree : 0≤τ-tauThree β := sub_nonneg.mpr ht3
    have hxi : 0≤2-ξ := sub_nonneg.mpr hξ.2
    positivity
  have hh := affine_pos hm0 hmax (div_nonneg hy hm.le) ((div_lt_one hm).mpr hym)
  rw [←mixed_affine_step] at hh
  simpa only [mul_zero,zero_add,div_mul_cancel₀ _ hm.ne'] using hh

theorem mixed_pos {β τ yμ y ξ : ℝ} (hβ : 0≤β) (hβ1 : β<1) (hτ : 0≤τ)
    (ht3 : tauThree β≤τ) (hts : τ<tauStar β) (hμ : 0<yμ) (hy : yμ<y)
    (hym : y<maxStep β τ) (hξ : ξ∈Ioc (0:ℝ) 2) :
    0<mixedPolynomial β τ (lagTwoWeight β τ) yμ y ξ := by
  have hy0 := hμ.trans hy
  have hl := lagTwoWeight_pos hβ hβ1 hτ hts
  have hd : 0<mixedPolynomial β τ (lagTwoWeight β τ) y y ξ := by
    rw [mixed_diagonal]
    exact mul_pos (by nlinarith [mul_nonneg hl.le (sub_nonneg.mpr hξ.2)])
      (diagonal_pos_of_nonzero ⟨hξ.1.le,hξ.2⟩
        (diagonal_nonzero_of_margin hβ hβ1 hτ hy0 hym))
  have hh := affine_pos (mixed_zero_mu_pos hβ hβ1 hτ ht3 hts hy0.le hym hξ) hd.le
    (div_nonneg hμ.le hy0.le) ((div_lt_one hy0).mpr hy)
  rw [←mixed_affine_mu] at hh
  simpa only [mul_zero,zero_add,div_mul_cancel₀ _ hy0.ne'] using hh

end
end nesterov.FiniteCondition
