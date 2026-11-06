import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Quantitative Fourier data used by the half-step spreading argument.
The concrete normalized smooth convolution is constructed in `Kernel`. -/
namespace nesterov.Spread
noncomputable section
open Set

structure KernelData where
  hat : ℝ → ℝ
  a0 : ℝ
  ck : ℝ
  Ck : ℝ
  a0_pos : 0<a0
  ck_pos : 0<ck
  ck_le_half : ck≤1/2
  Ck_pos : 0<Ck
  hat_mem : ∀ x : ℝ,hat x∈Icc (0:ℝ) 1
  hat_even : ∀ x : ℝ,hat (-x)=hat x
  hat_zero : hat 0=1
  continuous_hat : Continuous hat
  hat_half : ∀ {a : ℝ},0<a → a≤a0 → 1/2≤hat a
  gap : ∀ {a x : ℝ},0<a → a≤a0 → 3*a≤x →
    hat x≤hat a-ck*min (x^2) 1
  decay : ∀ {x : ℝ},x≠0 → |hat x|≤Ck/x^2

namespace KernelData

def s1 (D : KernelData) : ℝ := min (1/6) (3*D.a0/Real.pi)

def longConstant (D : KernelData) : ℝ := 16*D.Ck

theorem s1_pos (D : KernelData) : 0<D.s1 := by
  exact lt_min (by norm_num) (div_pos (mul_pos (by norm_num) D.a0_pos) Real.pi_pos)

theorem s1_le_one_sixth (D : KernelData) : D.s1≤1/6 := min_le_left _ _

theorem s1_scale_le_a0 (D : KernelData) : Real.pi*D.s1/3≤D.a0 := by
  have h := (le_div_iff₀ Real.pi_pos).mp (min_le_right (1/6:ℝ) (3*D.a0/Real.pi))
  change Real.pi*min (1/6:ℝ) (3*D.a0/Real.pi)/3≤D.a0
  nlinarith

theorem longConstant_pos (D : KernelData) : 0<D.longConstant := by
  exact mul_pos (by norm_num) D.Ck_pos

end KernelData
end
end nesterov.Spread
