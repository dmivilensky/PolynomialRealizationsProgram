import polyak.General.Multipliers.Algebra
import polyak.General.Roots

/-! Appendix D, Lemma symbols: both orientations of the actual wave symbol,
including all polynomial denominators and the reciprocal-circle identity. -/

namespace polyak.General.Multipliers
noncomputable section
open scoped BigOperators

theorem wave_reciprocal (t w : ℝ) :
    Waves.z t w = (star (Waves.z (-t) w))⁻¹ := by
  simp only [Waves.z, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  apply Complex.ext <;> simp

theorem b_ne_zero_outside (q : Tuning) {z : ℂ} (hz : q.rhoB < ‖z‖) : q.b z ≠ 0 := by
  intro h
  exact hz.not_ge (root_norm_le q.beta_nonneg h)

theorem a_ne_zero_outside (q : Tuning) {z : ℂ} (hz : q.rhoA < ‖z‖) : q.a z ≠ 0 := by
  intro h
  exact hz.not_ge (root_norm_le q.beta_nonneg h)

theorem lower_positive_actual (q : Tuning) (s : Finset ℕ) (lam : ℕ → ℝ)
    {t : ℝ} (ht : 0 ≤ t) (c : Spectral.Frequency) :
    Duality.symbol (Waves.multiplierMap q.A q.B q.beta t) t s
      (fun n => lam n*Real.exp (-(n*t))) (fun _ => 0) 0
      (∑ n ∈ s, lam n*Real.exp (-(n*t))*Real.sinh (n*t)) c =
      -(Complex.normSq (aSharp q (Waves.z (-t) (Real.arccos c))) /
        (q.B^2*Complex.normSq (Waves.z (-t) (Real.arccos c)))) *
      (polynomial s lam (Waves.z (-t) (Real.arccos c))*
        bSharp q (Waves.z (-t) (Real.arccos c))/
        aSharp q (Waves.z (-t) (Real.arccos c))).re := by
  rw [lower_positive_symbol]
  dsimp only [Duality.g, Waves.multiplierMap, ContinuousMap.coe_mk]
  rw [← q.m_wave]
  rw [Tuning.real_im_factor, wave_reciprocal]
  apply factor_sharp_re_lower q (Waves.z_ne_zero _ _)
  apply aSharp_ne_zero q
  have hn := Waves.norm_z_pow (-t) (Real.arccos c) 1
  simp only [pow_one, Nat.cast_one, one_mul] at hn
  rw [hn, Real.exp_le_one_iff]
  exact neg_nonpos.mpr ht

theorem lower_negative_actual (q : Tuning) (s : Finset ℕ) (lam : ℕ → ℝ)
    (t : ℝ) (c : Spectral.Frequency)
    (hb : q.rhoB < Real.exp t) :
    Duality.symbol (Waves.multiplierMap q.A q.B q.beta t) t s
      (fun n => lam n*Real.exp (n*t)) (fun _ => 0)
      (-(∑ n ∈ s, lam n*Real.exp (n*t)*Real.sinh (n*t))) 0 c =
      -(Complex.normSq (q.b (Waves.z t (Real.arccos c))) /
        (q.B^2*Complex.normSq (Waves.z t (Real.arccos c)))) *
      (polynomial s lam (Waves.z t (Real.arccos c))*q.a (Waves.z t (Real.arccos c))/
        q.b (Waves.z t (Real.arccos c))).re := by
  rw [lower_negative_symbol]
  dsimp only [Duality.g, Waves.multiplierMap, ContinuousMap.coe_mk]
  rw [← q.m_wave]
  rw [Tuning.real_im_factor]
  apply factor_re_lower q (Waves.z_ne_zero _ _)
  apply b_ne_zero_outside q
  have hn := Waves.norm_z_pow t (Real.arccos c) 1
  simp only [pow_one, Nat.cast_one, one_mul] at hn
  rw [hn]
  exact hb

theorem upper_positive_actual (q : Tuning) (s : Finset ℕ) (lam : ℕ → ℝ)
    {t : ℝ} (ht : 0 ≤ t) (c : Spectral.Frequency) :
    Duality.symbol (Waves.multiplierMap q.A q.B q.beta t) t s
      (fun _ => 0) (fun n => lam n*Real.exp (-(n*t)))
      (∑ n ∈ s, lam n*Real.exp (-(n*t))*Real.sinh (n*t)) 0 c =
      -(Complex.normSq (bSharp q (Waves.z (-t) (Real.arccos c))) /
        (q.B^2*Complex.normSq (Waves.z (-t) (Real.arccos c)))) *
      (polynomial s lam (Waves.z (-t) (Real.arccos c))*
        aSharp q (Waves.z (-t) (Real.arccos c))/
        bSharp q (Waves.z (-t) (Real.arccos c))).re := by
  rw [upper_positive_symbol]
  dsimp only [Duality.g, Waves.multiplierMap, ContinuousMap.coe_mk]
  rw [← q.m_wave]
  rw [Tuning.real_im_factor, wave_reciprocal]
  apply factor_sharp_re_upper q (Waves.z_ne_zero _ _)
  apply bSharp_ne_zero q
  have hn := Waves.norm_z_pow (-t) (Real.arccos c) 1
  simp only [pow_one, Nat.cast_one, one_mul] at hn
  rw [hn, Real.exp_le_one_iff]
  exact neg_nonpos.mpr ht

theorem upper_negative_actual (q : Tuning) (s : Finset ℕ) (lam : ℕ → ℝ)
    (t : ℝ) (c : Spectral.Frequency)
    (hb : q.rhoA < Real.exp t) :
    Duality.symbol (Waves.multiplierMap q.A q.B q.beta t) t s
      (fun _ => 0) (fun n => lam n*Real.exp (n*t))
      0 (-(∑ n ∈ s, lam n*Real.exp (n*t)*Real.sinh (n*t))) c =
      -(Complex.normSq (q.a (Waves.z t (Real.arccos c))) /
        (q.B^2*Complex.normSq (Waves.z t (Real.arccos c)))) *
      (polynomial s lam (Waves.z t (Real.arccos c))*q.b (Waves.z t (Real.arccos c))/
        q.a (Waves.z t (Real.arccos c))).re := by
  rw [upper_negative_symbol]
  dsimp only [Duality.g, Waves.multiplierMap, ContinuousMap.coe_mk]
  rw [← q.m_wave]
  rw [Tuning.real_im_factor]
  apply factor_re_upper q (Waves.z_ne_zero _ _)
  apply a_ne_zero_outside q
  have hn := Waves.norm_z_pow t (Real.arccos c) 1
  simp only [pow_one, Nat.cast_one, one_mul] at hn
  rw [hn]
  exact hb

end
end polyak.General.Multipliers
