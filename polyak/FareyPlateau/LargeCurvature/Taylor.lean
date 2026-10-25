import polyak.ModeLocking.Analysis.JetBounds

noncomputable section
namespace polyak.FareyPlateau.LargeCurvature
open Set

def tangentLine (c bar z x : ℝ) : ℝ := c+bar*(x-z)/2
def tangentRemainder (f : ℝ→ℝ) (c bar z x : ℝ) : ℝ := f x-tangentLine c bar z x

theorem tangentLine_deriv (c bar z x : ℝ) : deriv (tangentLine c bar z) x=bar/2 := by
  have hh := (((hasDerivAt_id x).sub_const z).const_mul bar).div_const 2
  change deriv (fun y=>c+bar*(y-z)/2) x=bar/2
  simpa only [mul_one,id_eq] using (hh.const_add c).deriv

theorem tangentLine_second (c bar z x : ℝ) : iteratedDeriv 2 (tangentLine c bar z) x=0 := by
  have he : deriv (tangentLine c bar z)=fun _=>bar/2 := funext (tangentLine_deriv c bar z)
  simp only [iteratedDeriv_succ,iteratedDeriv_zero]
  change deriv (deriv (tangentLine c bar z)) x=0
  rw [he,deriv_const]

theorem tangentRemainder_second {f : ℝ→ℝ} {x : ℝ} (hf : ContDiffAt ℝ 2 f x)
    (c bar z : ℝ) : iteratedDeriv 2 (tangentRemainder f c bar z) x=iteratedDeriv 2 f x := by
  have hl : ContDiffAt ℝ 2 (tangentLine c bar z) x := by unfold tangentLine; fun_prop
  change iteratedDeriv 2 (fun y=>f y-tangentLine c bar z y) x=_
  rw [iteratedDeriv_fun_sub hf hl,tangentLine_second,sub_zero]

theorem tangent_quadratic_lower {f : ℝ→ℝ} {a b z x c bar m : ℝ}
    (hf : ∀ y∈Icc a b, ContDiffAt ℝ 2 f y) (hz : z∈Icc a b) (hx : x∈Icc a b)
    (hvalue : f z=c) (hslope : 2*deriv f z=bar)
    (hbound : ∀ y∈uIcc z x,m ≤ iteratedDeriv 2 f y) :
    m/2*(x-z)^2 ≤ tangentRemainder f c bar z x := by
  have hsmooth (y) (hy : y∈Icc a b) : ContDiffAt ℝ 2 (tangentRemainder f c bar z) y := by
    exact (hf y hy).sub (by unfold tangentLine; fun_prop)
  have hzero : tangentRemainder f c bar z z=0 := by simp [tangentRemainder,tangentLine,hvalue]
  have hderiv : deriv (tangentRemainder f c bar z) z=0 := by
    have hl : DifferentiableAt ℝ (tangentLine c bar z) z := by unfold tangentLine; fun_prop
    change deriv (fun y=>f y-tangentLine c bar z y) z=0
    rw [deriv_fun_sub ((hf z hz).differentiableAt (by norm_num)) hl,tangentLine_deriv]
    linarith
  by_cases he : z=x
  · subst x
    simp [hzero]
  obtain ⟨y,hy,hyform⟩ := ModeLocking.Analysis.quadratic_taylor hsmooth hz hx he hzero hderiv
  rw [hyform,tangentRemainder_second (hf y (uIcc_subset_Icc hz hx (Ioo_subset_Icc_self hy)))]
  have hm := mul_le_mul_of_nonneg_right (hbound y (Ioo_subset_Icc_self hy)) (sq_nonneg (x-z))
  nlinarith

end polyak.FareyPlateau.LargeCurvature
