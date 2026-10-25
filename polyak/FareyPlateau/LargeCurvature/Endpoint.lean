import polyak.FareyPlateau.LargeCurvature.ZoneC

noncomputable section
namespace polyak.FareyPlateau.LargeCurvature
open General Levels Set
open scoped BigOperators
namespace SourceData
variable {q : Tuning} {j k : ℕ} (B : SourceData q j k)

theorem zero_outside : (0:ℝ) ∉ B.window := by
  intro hz
  have hh := B.window_trimmed hz
  have hp : 0 < Real.pi/(2*k) := div_pos Real.pi_pos (mul_pos (by norm_num) B.kp)
  linarith [hh.1]

theorem tau_bound : Geometry.tau q ≤ 2/(B.a*B.ε^2) := by
  have hX := B.far_profile (show (0:ℝ)∈Icc (0:ℝ) Real.pi from ⟨le_rfl,Real.pi_pos.le⟩) B.zero_outside
  rw [Real.cos_zero] at hX
  have hA : 0 < B.a*B.ε^2 := mul_pos B.a_pos (sq_pos_of_pos B.epsilon_pos)
  have hden : B.a*B.ε^2/2 ≤ -q.Xi 1 := by linarith
  have hh := div_le_div_of_nonneg_left (show (0:ℝ) ≤ 1 by norm_num) (half_pos hA) hden
  have he : (1:ℝ)/(B.a*B.ε^2/2)=2/(B.a*B.ε^2) := by ring
  rw [he] at hh
  calc
    Geometry.tau q = 1/(-q.Xi 1) := by unfold Geometry.tau; ring
    _ ≤ _ := hh

theorem endpoint : 0 < ∑ i,B.w i*(B.n i:ℝ)*((B.n i:ℝ)+2*Geometry.tau q) := by
  have hA : 0 < B.a*B.ε^2 := mul_pos B.a_pos (sq_pos_of_pos B.epsilon_pos)
  have hτ := Geometry.tau_pos q
  have hbar := (abs_le.mp B.bar_abs).1
  have hfirst : -2*Geometry.tau q*B.N ≤ 2*Geometry.tau q*B.bar := by
    nlinarith [mul_le_mul_of_nonneg_left hbar (show 0 ≤ 2*Geometry.tau q by positivity)]
  have htau : -(4*B.N/(B.a*B.ε^2)) ≤ -2*Geometry.tau q*B.N := by
    have hh := mul_le_mul_of_nonneg_right B.tau_bound (show 0 ≤ 2*B.N by positivity [B.N_pos])
    have he : 2/(B.a*B.ε^2)*(2*B.N)=4*B.N/(B.a*B.ε^2) := by ring
    rw [he] at hh
    linarith only [hh]
  have hstrict : 4*B.N/(B.a*B.ε^2) < (k:ℝ)^2/6 := by
    apply (div_lt_iff₀ hA).mpr
    have hh := (div_lt_iff₀ (sq_pos_of_pos B.kp)).mp B.extra_margins.2
    nlinarith
  have he : (∑ i,B.w i*(B.n i:ℝ)*((B.n i:ℝ)+2*Geometry.tau q)) =
      (∑ i,B.w i*(B.n i:ℝ)^2)+2*Geometry.tau q*B.bar := by
    rw [←B.mean]
    simp only [Fin.sum_univ_succ]
    ring
  rw [he]
  have hh := add_le_add B.moment (htau.trans hfirst)
  exact lt_of_lt_of_le (by linarith only [hstrict]) hh

end SourceData
end polyak.FareyPlateau.LargeCurvature
