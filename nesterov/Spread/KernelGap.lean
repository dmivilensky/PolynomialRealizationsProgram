import nesterov.Spread.KernelData
import polyak.Global.Kernels.GainLarge
import polyak.Global.Kernels.Variation
import Mathlib.Analysis.Real.Pi.Bounds

/-! A quantitative relative Fourier gap for the actual smooth convolution.
All constants are selected from the fixed normalized Polyak bump. -/
namespace nesterov.Spread
noncomputable section
open Set
open polyak.Global.Kernels

theorem phiHat_even (x : ℝ) : phiHat (-x)=phiHat x := by
  rw [phiHat_integral_cos,phiHat_integral_cos]
  congr 1
  funext u
  simp only [neg_mul,Real.cos_neg]

theorem phiHat_quadratic_upper (a : ℝ) :
    1-phiHat a≤mPhi*a^2/2 := by
  have h := phiHat_difference_quadratic a 0
  simp only [phiHat_zero,add_zero,sub_zero] at h
  rw [mul_assoc,abs_mul_abs_self,←pow_two] at h
  have hl := (neg_le_abs (phiHat a-1)).trans h
  linarith

theorem exists_relative_fourier_gap :
    ∃ a0 ck : ℝ,0<a0 ∧ 0<ck ∧ ck≤1/2 ∧
      (∀ a : ℝ,0<a → a≤a0 → 1/2≤phiHat a) ∧
      ∀ a x : ℝ,0<a → a≤a0 → 3*a≤x →
        phiHat x≤phiHat a-ck*min (x^2) 1 := by
  obtain ⟨g,hg,hlarge⟩ := phiHat_gap_large
  let a0 : ℝ := min 1 (min (1/(mPhi+1)) (g/(mPhi+1)))
  let ck : ℝ := min (1/2) (min (mPhi/24) (g/2))
  have hm : 0<mPhi := mPhi_pos
  have ha0 : 0<a0 := lt_min (by norm_num)
    (lt_min (by positivity) (by positivity))
  have hck : 0<ck := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hsmall (a : ℝ) (ha : 0<a) (haa : a≤a0) :
      mPhi*a^2≤1 ∧ mPhi*a^2≤g := by
    have ha1 : a≤1 := haa.trans (min_le_left _ _)
    have haM : a≤1/(mPhi+1) := haa.trans ((min_le_right _ _).trans (min_le_left _ _))
    have haG : a≤g/(mPhi+1) := haa.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hM := (le_div_iff₀ (by positivity : 0<mPhi+1)).mp haM
    have hG := (le_div_iff₀ (by positivity : 0<mPhi+1)).mp haG
    have hasq : a^2≤a := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hasq hm.le
    exact ⟨by nlinarith,by nlinarith⟩
  refine ⟨a0,ck,ha0,hck,min_le_left _ _,?_,?_⟩
  · intro a ha haa
    have hs := (hsmall a ha haa).1
    have hu := phiHat_quadratic_upper a
    linarith
  · intro a x ha haa hax
    have hx : 0<x := (mul_pos (by norm_num) ha).trans_le hax
    have hmin : ck*min (x^2) 1≤ck*x^2 :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) hck.le
    by_cases hsmallx : x≤2*Real.pi
    · have hlow := phiHat_gain_small (ξ:=x) (by rwa [abs_of_pos hx])
      have hπ : Real.pi^2≤16 := by nlinarith [Real.pi_lt_four,Real.pi_pos]
      have hp : (1/8:ℝ)≤2/Real.pi^2 :=
        (le_div_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr (by nlinarith)
      have hmul := mul_le_mul_of_nonneg_right hp (mul_nonneg hm.le (sq_nonneg x))
      have hlow' : (mPhi/8)*x^2≤1-phiHat x := by nlinarith
      have haBound : a^2≤x^2/9 := by nlinarith
      have hprod := mul_le_mul_of_nonneg_left haBound hm.le
      have hupper := phiHat_quadratic_upper a
      have hckM : ck≤mPhi/24 := (min_le_right _ _).trans (min_le_left _ _)
      have hcx := mul_le_mul_of_nonneg_right hckM (sq_nonneg x)
      nlinarith
    · have hh := hlarge x (by rw [abs_of_pos hx];exact le_of_not_ge hsmallx)
      have hupper := phiHat_quadratic_upper a
      have hag := (hsmall a ha haa).2
      have hckG : ck≤g/2 := (min_le_right _ _).trans (min_le_right _ _)
      have hmc : ck*min (x^2) 1≤ck := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (min_le_right (x^2) 1) hck.le
      nlinarith

end
end nesterov.Spread
