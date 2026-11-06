import nesterov.TwoStep.Band
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Uniform geometry of the relative rational-frequency bands used by
the spread witnesses. -/
namespace nesterov.TwoStep.Spread
noncomputable section
open Set

def band (s ω₀ : ℝ) : Set ℝ := Icc ((1-s)*ω₀) ((1+s)*ω₀)
def xiMax (s ω₀ : ℝ) : ℝ := 1-Real.cos ((1+s)*ω₀)
def endpointReserve : ℝ := 1+Real.cos (7*Real.pi/9)

theorem endpointReserve_pos : 0<endpointReserve := by
  have hc : Real.cos Real.pi<Real.cos (7*Real.pi/9) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity)
      le_rfl (by linarith [Real.pi_pos])
  rw [Real.cos_pi] at hc
  unfold endpointReserve
  linarith

theorem band_mem_Ioo {s ω₀ ω : ℝ} (hs : s∈Ioc (0:ℝ) (1/6))
    (hω₀ : ω₀∈Ioc (0:ℝ) (2*Real.pi/3)) (hω : ω∈band s ω₀) :
    ω∈Ioo (0:ℝ) Real.pi := by
  have hlo : 0<(1-s)*ω₀ := mul_pos (by linarith [hs.2]) hω₀.1
  have hhi : (1+s)*ω₀≤7*Real.pi/9 := by
    nlinarith [hω₀.2,mul_nonneg (show 0≤1/6-s by linarith [hs.2]) hω₀.1.le]
  exact ⟨hlo.trans_le hω.1,hω.2.trans_lt (hhi.trans_lt (by linarith [Real.pi_pos]))⟩

theorem band_two_sub_xi_lower {s ω₀ ω : ℝ} (hs : s∈Ioc (0:ℝ) (1/6))
    (hω₀ : ω₀∈Ioc (0:ℝ) (2*Real.pi/3)) (hω : ω∈band s ω₀) :
    endpointReserve≤2-(1-Real.cos ω) := by
  have hmem := band_mem_Ioo hs hω₀ hω
  have hhi : ω≤7*Real.pi/9 := by
    have hh : (1+s)*ω₀≤7*Real.pi/9 := by
      nlinarith [hω₀.2,mul_nonneg (show 0≤1/6-s by linarith [hs.2]) hω₀.1.le]
    exact hω.2.trans hh
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi hmem.1.le
    (by linarith [Real.pi_pos] : 7*Real.pi/9≤Real.pi) hhi
  unfold endpointReserve
  linarith

theorem xiMax_pos {s ω₀ : ℝ} (hs : s∈Ioc (0:ℝ) (1/6))
    (hω₀ : ω₀∈Ioc (0:ℝ) (2*Real.pi/3)) : 0<xiMax s ω₀ := by
  have hu : (1+s)*ω₀∈band s ω₀ := ⟨by nlinarith [mul_pos hs.1 hω₀.1],le_rfl⟩
  have hm := band_mem_Ioo hs hω₀ hu
  exact sub_pos.mpr (by simpa only [Real.cos_zero] using
    Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ)≤0) hm.2.le hm.1)

theorem xiMax_le_square {s ω₀ : ℝ} (hs : s∈Ioc (0:ℝ) (1/6))
    (hω₀ : 0<ω₀) : xiMax s ω₀≤ω₀^2 := by
  have hu : (1+s)*ω₀≤(7/6)*ω₀ := by nlinarith [mul_nonneg (show 0≤1/6-s by linarith [hs.2]) hω₀.le]
  have hl : 0≤(1+s)*ω₀ := by positivity [hs.1]
  have hsquare := (sq_le_sq₀ hl (by positivity : 0≤(7/6)*ω₀)).mpr hu
  have hc := Real.one_sub_sq_div_two_le_cos (x:=(1+s)*ω₀)
  unfold xiMax
  nlinarith [sq_nonneg ω₀]

private theorem sin_ratio_lower {a b : ℝ} (ha : 0≤a) (hb : 0<b)
    (hab : a≤b) (hbπ : b≤Real.pi) : (a/b)*Real.sin b≤Real.sin a := by
  have h := strictConcaveOn_sin_Icc.concaveOn.2
    (show (0:ℝ)∈Icc (0:ℝ) Real.pi from ⟨le_rfl,Real.pi_pos.le⟩)
    (show b∈Icc (0:ℝ) Real.pi from ⟨hb.le,hbπ⟩)
    (show 0≤1-a/b from sub_nonneg.mpr ((div_le_one hb).mpr hab))
    (div_nonneg ha hb.le) (show 1-a/b+a/b=1 by ring)
  simpa only [smul_eq_mul,Real.sin_zero,mul_zero,zero_add,div_mul_cancel₀ _ hb.ne'] using h

private theorem xi_sin_half (ω : ℝ) : 1-Real.cos ω=2*Real.sin (ω/2)^2 := by
  have hc := Real.cos_two_mul (ω/2)
  rw [mul_div_cancel₀ _ (by norm_num : (2:ℝ)≠0)] at hc
  nlinarith [Real.sin_sq_add_cos_sq (ω/2)]

theorem band_xi_comparable {s ω₀ ω : ℝ} (hs : s∈Ioc (0:ℝ) (1/6))
    (hω₀ : ω₀∈Ioc (0:ℝ) (2*Real.pi/3)) (hω : ω∈band s ω₀) :
    xiMax s ω₀/2≤1-Real.cos ω ∧ 1-Real.cos ω≤xiMax s ω₀ := by
  have hm := band_mem_Ioo hs hω₀ hω
  have hu : (1+s)*ω₀∈band s ω₀ := ⟨by nlinarith [mul_pos hs.1 hω₀.1],le_rfl⟩
  have hmu := band_mem_Ioo hs hω₀ hu
  have hωp := hω₀.1
  have hden : 0<1+s := by linarith [hs.1]
  let k : ℝ := (1-s)/(1+s)
  have hk : 5/7≤k := (le_div_iff₀ hden).mpr (by linarith [hs.2])
  have hk0 : 0≤k := le_trans (by norm_num) hk
  have hratio : k≤(ω/2)/(((1+s)*ω₀)/2) := by
    apply (le_div_iff₀ (by positivity : 0<((1+s)*ω₀)/2)).mpr
    have heq : k*(((1+s)*ω₀)/2)=(1-s)*ω₀/2 := by
      dsimp [k]
      field_simp
    rw [heq]
    linarith [hω.1]
  have hbpos : 0<((1+s)*ω₀)/2 := by positivity
  have hsB : 0≤Real.sin (((1+s)*ω₀)/2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hbpos.le (by linarith [hmu.2,Real.pi_pos])
  have hsA : 0≤Real.sin (ω/2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hm.1]) (by linarith [hm.2,Real.pi_pos])
  have hsin : k*Real.sin (((1+s)*ω₀)/2)≤Real.sin (ω/2) :=
    (mul_le_mul_of_nonneg_right hratio hsB).trans
      (sin_ratio_lower (by linarith [hm.1]) hbpos (by linarith [hω.2]) (by linarith [hmu.2,Real.pi_pos]))
  have hsq := (sq_le_sq₀ (mul_nonneg hk0 hsB) hsA).mpr hsin
  have hk2 : (1/2:ℝ)≤k^2 := by
    have hh := (sq_le_sq₀ (by norm_num : (0:ℝ)≤5/7) hk0).mpr hk
    norm_num at hh
    linarith
  constructor
  · unfold xiMax
    rw [xi_sin_half,xi_sin_half]
    have hh := mul_le_mul_of_nonneg_right hk2 (sq_nonneg (Real.sin (((1+s)*ω₀)/2)))
    rw [mul_pow] at hsq
    nlinarith
  · unfold xiMax
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi hm.1.le hmu.2.le hω.2
    linarith

end
end nesterov.TwoStep.Spread
