import polyak.Global.Kernels.GainLarge

/-! Article lem:A-gain, for all real scales and frequencies. -/
noncomputable section
namespace polyak.Global.Kernels
open MeasureTheory Set Function

theorem exists_gain_constant : ∃c:ℝ,0<c ∧ ∀ε ξ:ℝ,
    c*min (ε^2*ξ^2) 1≤1-kernelHat ε ξ := by
  obtain ⟨b,hb,hlarge⟩ := phiHat_gap_large
  let a : ℝ := (2/Real.pi^2)*mPhi
  have ha : 0<a := mul_pos (div_pos (by norm_num) (pow_pos Real.pi_pos 2)) mPhi_pos
  refine ⟨min a b,lt_min ha hb,?_⟩
  intro ε ξ
  have hmin : 0≤min (ε^2*ξ^2) 1 := le_min (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (by norm_num)
  by_cases hs : |ε*ξ|≤2*Real.pi
  · have hh := kernelHat_gain_small hs
    have hp := mul_le_mul_of_nonneg_right (min_le_left a b) hmin
    have hq := mul_le_mul_of_nonneg_left (min_le_left (ε^2*ξ^2) 1) ha.le
    dsimp [a] at hp hq
    nlinarith [hh]
  · have hh := hlarge (ε*ξ) (le_of_lt (lt_of_not_ge hs))
    obtain ⟨hl,hu⟩ := phiHat_mem (ε*ξ)
    have hp := mul_le_mul_of_nonneg_left (min_le_right (ε^2*ξ^2) 1)
      (le_min ha.le hb.le)
    have hq := min_le_right a b
    unfold kernelHat
    nlinarith

def gainConstant : ℝ := Classical.choose exists_gain_constant

theorem gainConstant_pos : 0<gainConstant := (Classical.choose_spec exists_gain_constant).1

theorem kernelHat_gain (ε ξ:ℝ) :
    gainConstant*min (ε^2*ξ^2) 1≤1-kernelHat ε ξ :=
  (Classical.choose_spec exists_gain_constant).2 ε ξ

end polyak.Global.Kernels
