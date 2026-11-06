import chebyshev1.Stepsize.PrefixComparison
import chebyshev1.Prefix.Asymptotics

/-! Asymptotic size of the strict finite-horizon stepsize/prefix separation. -/
namespace chebyshev1.Stepsize
noncomputable section
open Real Filter Topology Asymptotics

theorem leadingBound_div_prefix (I : SpectralInterval) {N : ℕ} (hN : 0 < N) :
    leadingBound I N / Prefix.leadingGain I N = sqrt ((N : ℝ) / 2) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have he : I.epsilon N ≠ 0 := (one_div_pos.mpr (I.den_pos N)).ne'
  have hn0 : sqrt (N : ℝ) ≠ 0 := (sqrt_pos.mpr hn).ne'
  have h₂ : sqrt (2 : ℝ) ≠ 0 := (sqrt_pos.mpr (by norm_num)).ne'
  have h₃ : sqrt (3 : ℝ) ≠ 0 := (sqrt_pos.mpr (by norm_num)).ne'
  dsimp only [leadingBound, Prefix.leadingGain]
  rw [sqrt_div (by norm_num : (0 : ℝ) ≤ 2), sqrt_div hn.le]
  field_simp [he, hn0, h₂, h₃, I.delta_pos.ne']
  nlinarith [sq_sqrt hn.le, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem lowerBound_div_prefix_isEquivalent (I : SpectralInterval) :
    (fun N : ℕ => lowerBound I N / (Prefix.realization I).gain I N) ~[atTop]
      (fun N : ℕ => sqrt ((N : ℝ) / 2)) := by
  apply ((lowerBound_asymptotic I).div (Prefix.gain_isEquivalent I)).congr_right
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  exact leadingBound_div_prefix I hN

end
end chebyshev1.Stepsize
