import nesterov.Spread.Slacks

/-! The quantitative hyperbolic bounds used for every lag. -/
namespace nesterov.Spread
noncomputable section

theorem eMinus_expansion (η x : ℝ) :
    eMinus η x=(1-η/2)*Real.exp (-x)+(η/2)*Real.exp x := by
  rw [eMinus,Real.cosh_eq,Real.sinh_eq]
  ring

theorem ePlus_expansion (η x : ℝ) :
    ePlus η x=(η/2)*Real.exp (-x)+(1-η/2)*Real.exp x := by
  rw [ePlus,Real.cosh_eq,Real.sinh_eq]
  ring

theorem eMinus_ge_exp {η x : ℝ} (hη : 0≤η) (hx : 0≤x) :
    Real.exp (-x)≤eMinus η x := by
  have h := mul_nonneg hη (Real.sinh_nonneg_iff.mpr hx)
  have he := Real.cosh_sub_sinh x
  unfold eMinus
  linarith

theorem ePlus_ge_one {η x : ℝ} (hη1 : η≤1) (hx : 0≤x) : 1≤ePlus η x := by
  have h := mul_nonneg (sub_nonneg.mpr hη1) (Real.sinh_nonneg_iff.mpr hx)
  exact (Real.one_le_cosh x).trans (by unfold ePlus;linarith)

theorem ePlus_ge_eMinus {η x : ℝ} (hη1 : η≤1) (hx : 0≤x) :
    eMinus η x≤ePlus η x := by
  have h := mul_nonneg (sub_nonneg.mpr hη1) (Real.sinh_nonneg_iff.mpr hx)
  unfold ePlus eMinus
  linarith

theorem eMinus_ge_sqrt {η x : ℝ} (hη : 0≤η) (hη1 : η≤1) :
    Real.sqrt η≤eMinus η x := by
  let u := (1-η/2)*Real.exp (-x)
  let v := (η/2)*Real.exp x
  have hu : 0≤u := mul_nonneg (by linarith) (Real.exp_pos _).le
  have hv : 0≤v := mul_nonneg (by linarith) (Real.exp_pos _).le
  have he : eMinus η x=u+v := eMinus_expansion η x
  have hmul : u*v=η*(2-η)/4 := by
    dsimp [u,v]
    calc
      _=((1-η/2)*(η/2))*(Real.exp (-x)*Real.exp x) := by ring
      _=η*(2-η)/4 := by rw [←Real.exp_add,neg_add_cancel,Real.exp_zero];ring
  apply (Real.sqrt_le_iff).mpr
  constructor
  · rw [he]
    positivity
  · rw [he]
    have hηsq : η^2≤η := by nlinarith
    nlinarith [sq_nonneg (u-v)]

theorem eMinus_ge_growing_exp {η x : ℝ} (_hη : 0≤η) (hη1 : η≤1) :
    (η/2)*Real.exp x≤eMinus η x := by
  rw [eMinus_expansion]
  exact le_add_of_nonneg_left (mul_nonneg (by linarith) (Real.exp_pos _).le)

end
end nesterov.Spread
