import nesterov.Trace.Disk
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! Conjugation-invariant functions on the unit circle are determined by the
closed upper semicircle; continuity fills in its two real endpoints. -/
namespace nesterov.Trace
noncomputable section
open Complex Metric Set Real

theorem unit_circle_representation {z : ℂ} (hz : Complex.normSq z=1) :
    ∃ ω∈Icc (0:ℝ) Real.pi,z=Complex.exp ((ω:ℂ)*Complex.I) ∨
      z=star (Complex.exp ((ω:ℂ)*Complex.I)) := by
  have hs : z.re^2+z.im^2=1 := by simpa only [Complex.normSq_apply,←pow_two] using hz
  have hr : -1≤z.re ∧ z.re≤1 := by constructor <;> nlinarith [sq_nonneg z.im]
  let ω := Real.arccos z.re
  have hc : Real.cos ω=z.re := Real.cos_arccos hr.1 hr.2
  have hi : Real.sin ω=|z.im| := by
    rw [Real.sin_arccos,show 1-z.re^2=z.im^2 by nlinarith,Real.sqrt_sq_eq_abs]
  have hre : (Complex.exp ((ω:ℂ)*Complex.I)).re=z.re := by
    rw [Complex.exp_mul_I,←Complex.ofReal_cos,←Complex.ofReal_sin]
    simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,
      Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero,hc]
  have him : (Complex.exp ((ω:ℂ)*Complex.I)).im=|z.im| := by
    rw [Complex.exp_mul_I,←Complex.ofReal_cos,←Complex.ofReal_sin]
    simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,
      Complex.I_im,mul_one,zero_mul,add_zero,zero_add,hi]
  refine ⟨ω,⟨Real.arccos_nonneg _,Real.arccos_le_pi _⟩,?_⟩
  by_cases h : 0≤z.im
  · left
    apply Complex.ext
    · exact hre.symm
    · simpa only [abs_of_nonneg h] using him.symm
  · right
    apply Complex.ext
    · simpa only [Complex.star_def,Complex.conj_re] using hre.symm
    · simp only [Complex.star_def,Complex.conj_im,him,abs_of_neg (lt_of_not_ge h),neg_neg]

theorem nonneg_unit_of_upper {f : ℂ→ℝ}
    (hc : ContinuousOn f (sphere (0:ℂ) 1))
    (hconj : ∀ z∈sphere (0:ℂ) 1,f (star z)=f z)
    (hupper : ∀ ω∈Ioo (0:ℝ) Real.pi,0≤f (Complex.exp ((ω:ℂ)*Complex.I))) :
    ∀ z : ℂ,Complex.normSq z=1 → 0≤f z := by
  have hgc : Continuous (fun ω : ℝ=>f (Complex.exp ((ω:ℂ)*Complex.I))) :=
    hc.comp_continuous (by fun_prop) (fun ω=>by simp)
  have hclosed : IsClosed {ω : ℝ|0≤f (Complex.exp ((ω:ℂ)*Complex.I))} :=
    isClosed_le continuous_const hgc
  have hcc : Icc (0:ℝ) Real.pi⊆{ω : ℝ|0≤f (Complex.exp ((ω:ℂ)*Complex.I))} := by
    rw [←closure_Ioo (ne_of_lt Real.pi_pos)]
    exact closure_minimal hupper hclosed
  intro z hz
  obtain ⟨ω,hω,he|he⟩ := unit_circle_representation hz
  · rw [he]
    exact hcc hω
  · rw [he,hconj _ (by simp)]
    exact hcc hω

end
end nesterov.Trace
