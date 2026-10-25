import polyak.FareyPlateau.LargeCurvature.ThreeLag
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Uniform finite-symbol remainder estimates in the central zone. The
frequency displacement is free, and all lags are included in the finite sum. -/
noncomputable section
namespace polyak.FareyPlateau.LargeCurvature
open scoped BigOperators

variable {I : Type*} [Fintype I]

theorem cosine_error (w u : I→ℝ) (hw : ∀i,0≤w i) (hs : ∑i,w i=1) (δ : ℝ) :
    0≤1-∑i,w i*Real.cos (2*u i*δ) ∧
      1-∑i,w i*Real.cos (2*u i*δ) ≤ 2*(∑i,w i*u i^2)*δ^2 := by
  have hid : 1-∑i,w i*Real.cos (2*u i*δ)=∑i,w i*(1-Real.cos (2*u i*δ)) := by
    simp only [mul_sub,mul_one,Finset.sum_sub_distrib,hs]
  rw [hid]
  constructor
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (by linarith [Real.cos_le_one (2*u i*δ)]))
  · have hpoint (i:I) : w i*(1-Real.cos (2*u i*δ)) ≤ 2*w i*u i^2*δ^2 := by
      have hh := Real.one_sub_sq_div_two_le_cos (x:=2*u i*δ)
      have hp := mul_le_mul_of_nonneg_left hh (hw i)
      nlinarith only [hp]
    have hh := Finset.sum_le_sum (fun i (_:i∈Finset.univ)=>hpoint i)
    convert hh using 1
    simp only [Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem sine_error (w u : I→ℝ) (hw : ∀i,0≤w i)
    (hmean : ∑i,w i*u i=0) (δ : ℝ) :
    |∑i,w i*Real.sin (2*u i*δ)| ≤ (4/3)*(∑i,w i*|u i|^3)*|δ|^3 := by
  have hid : (∑i,w i*Real.sin (2*u i*δ))=
      ∑i,w i*(Real.sin (2*u i*δ)-2*u i*δ) := by
    simp only [mul_sub,Finset.sum_sub_distrib]
    have hh : ∑i,w i*(2*u i*δ)=2*(∑i,w i*u i)*δ := by
      simp only [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hh,hmean,mul_zero,zero_mul,sub_zero]
  rw [hid]
  have hpoint (i:I) : |w i*(Real.sin (2*u i*δ)-2*u i*δ)| ≤
      (4/3)*w i*|u i|^3*|δ|^3 := by
    rw [abs_mul,abs_of_nonneg (hw i),abs_sub_comm]
    have hh := mul_le_mul_of_nonneg_left (Real.abs_sub_sin_le (2*u i*δ)) (hw i)
    convert hh using 1
    rw [abs_mul,abs_mul]
    norm_num
    ring
  have hh := (Finset.abs_sum_le_sum_abs (fun i=>w i*(Real.sin (2*u i*δ)-2*u i*δ)) Finset.univ).trans (Finset.sum_le_sum (fun i _=>hpoint i))
  convert hh using 1
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

end polyak.FareyPlateau.LargeCurvature
