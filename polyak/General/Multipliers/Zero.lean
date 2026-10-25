import polyak.General.Multipliers.Disk

/-! Appendix D: eliminate the forced multiplier zero at the unit real point
by a balanced positive minimizer weight.  The result is strict on the whole
compact frequency interval, and hence bounds the actual original rate. -/

namespace polyak.General.Multipliers
noncomputable section
open Set

def oneFrequency : Spectral.Frequency := ⟨1, by norm_num, le_rfl⟩

theorem unit_wave_eq_one_iff (c : Spectral.Frequency) :
    Waves.z 0 (Real.arccos c) = 1 ↔ c = oneFrequency := by
  constructor
  · intro h
    have hr := congrArg Complex.re h
    have hz := Waves.z_pow_re 0 (Real.arccos c) 1
    simp only [pow_one, Nat.cast_one, one_mul, mul_zero, Real.exp_zero,
      Real.cos_arccos c.2.1 c.2.2, Complex.one_re] at hz hr
    apply Subtype.ext
    exact hz.symm.trans hr
  · rintro rfl
    simp [oneFrequency, Waves.z]

theorem g_one_negative (q : Tuning) :
    Duality.g (Waves.multiplierMap q.A q.B q.beta 0) oneFrequency < 0 := by
  have he : q.m 1 = ((1+q.beta-q.A)/q.B : ℝ) := by
    unfold Tuning.m
    push_cast
    simp
  have hm : 1 < (1+q.beta-q.A)/q.B := by
    apply (lt_div_iff₀ q.B_pos).2
    linarith [q.A_add_B, q.x_pos]
  change 1-Complex.normSq (q.m (Waves.z 0 (Real.arccos (oneFrequency : ℝ)))) < 0
  simp only [oneFrequency, Real.arccos_one, Waves.z, Complex.ofReal_zero,
    zero_mul, add_zero, Complex.exp_zero, he, Complex.normSq_ofReal]
  nlinarith

theorem lower_zero_certificate (q : Tuning) (s : Finset ℕ) (lam : ℕ → ℝ)
    (hs : ∀ n ∈ s, 1 ≤ n) (hlam : ∀ n ∈ s, 0 ≤ lam n)
    (hcircle : ∀ z : ℂ, ‖z‖ = 1 → z ≠ 1 → 0 < (polynomial s lam z*q.a z/q.b z).re) :
    Nonempty (Duality.StrictCertificate (Waves.multiplierMap q.A q.B q.beta 0) 0) := by
  let m := Waves.multiplierMap q.A q.B q.beta 0
  let f := Duality.symbol m 0 s lam (fun _ => 0) 0 0
  let g := Duality.g m
  have hB : q.rhoB < 1 := (le_max_right _ _).trans_lt q.rhoQ_lt_one
  have hphi (c : Spectral.Frequency) : f c =
      -(Complex.normSq (q.b (Waves.z 0 (Real.arccos c))) /
        (q.B^2*Complex.normSq (Waves.z 0 (Real.arccos c)))) *
      (polynomial s lam (Waves.z 0 (Real.arccos c))*q.a (Waves.z 0 (Real.arccos c))/
        q.b (Waves.z 0 (Real.arccos c))).re := by
    have h := lower_negative_actual q s lam 0 c (by simpa using hB)
    simpa only [mul_zero, Real.exp_zero, Real.sinh_zero, mul_one, mul_zero,
      Finset.sum_const_zero, neg_zero] using h
  have hc (c : Spectral.Frequency) : ‖Waves.z 0 (Real.arccos c)‖ = 1 := by
    have h := Waves.norm_z_pow 0 (Real.arccos c) 1
    simpa using h
  have hcoeff (c : Spectral.Frequency) : 0 <
      Complex.normSq (q.b (Waves.z 0 (Real.arccos c))) /
        (q.B^2*Complex.normSq (Waves.z 0 (Real.arccos c))) := by
    apply div_pos
    · exact Complex.normSq_pos.mpr (q.b_ne_zero_of_one_le_norm (hc c).ge)
    · exact mul_pos (sq_pos_of_pos q.B_pos) (Complex.normSq_pos.mpr (Waves.z_ne_zero _ _))
  have hfn : ∀ c, f c ≤ 0 := by
    intro c
    by_cases hc1 : c = oneFrequency
    · subst c
      rw [hphi, (unit_wave_eq_one_iff oneFrequency).2 rfl, polynomial_one]
      simp
    · rw [hphi]
      exact (mul_neg_of_neg_of_pos (neg_neg_of_pos (hcoeff c))
        (hcircle _ (hc c) (fun h => hc1 ((unit_wave_eq_one_iff c).1 h)))).le
  have hstrict : ∀ c, 0 ≤ g c → f c < 0 := by
    intro c hg
    have hc1 : c ≠ oneFrequency := by
      intro he; subst c; exact (g_one_negative q).not_ge hg
    rw [hphi]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos (hcoeff c))
      (hcircle _ (hc c) (fun h => hc1 ((unit_wave_eq_one_iff c).1 h)))
  obtain ⟨eta, heta, hnegative⟩ := balanced_perturbation f g
    (Duality.continuous_symbol _ _ _ _ _ _ _) (by unfold g Duality.g; fun_prop) hfn hstrict
  apply certificate_of_negative s lam (fun _ => 0) eta eta hs hlam
    (fun _ _ => le_rfl) heta.le heta.le
  · simp
  · intro c
    convert hnegative c using 1
    simp [f, g, Duality.symbol]
    ring

theorem lower_rate_lt_one (q : Tuning) (s : Finset ℕ) (lam : ℕ → ℝ)
    (hs : ∀ n ∈ s, 1 ≤ n) (hlam : ∀ n ∈ s, 0 ≤ lam n)
    (hmass : 0 < ∑ n ∈ s, lam n)
    (hcircle : ∀ z : ℂ, ‖z‖ = 1 → z ≠ 1 → 0 < (polynomial s lam z*q.a z/q.b z).re) :
    q.rate < 1 := by
  have hnonneg : ∀ z : ℂ, ‖z‖ = 1 → 0 ≤ (polynomial s lam z*q.a z/q.b z).re := by
    intro z hz
    by_cases hz1 : z = 1
    · simp [hz1]
    · exact (hcircle z hz hz1).le
  have hrate : q.rate < Real.exp 0 := by
    apply Growth.originalRate_lt_exp_of_certificates q.x_pos q.x_lt_y zero_lt_one q.beta_nonneg
    intro t ht
    rw [q.normalizedA_eq, q.normalizedB_eq]
    rcases ht.eq_or_lt with ht | ht
    · subst t; exact lower_zero_certificate q s lam hs hlam hcircle
    · exact lower_positive_certificate q s lam hs hlam hmass hnonneg ht
  simpa only [Real.exp_zero] using hrate

theorem upper_zero_certificate (q : Tuning) (s : Finset ℕ) (lam : ℕ → ℝ)
    (hs : ∀ n ∈ s, 1 ≤ n) (hlam : ∀ n ∈ s, 0 ≤ lam n)
    (hcircle : ∀ z : ℂ, ‖z‖ = 1 → z ≠ 1 → 0 < (polynomial s lam z*q.b z/q.a z).re) :
    Nonempty (Duality.StrictCertificate (Waves.multiplierMap q.A q.B q.beta 0) 0) := by
  let m := Waves.multiplierMap q.A q.B q.beta 0
  let f := Duality.symbol m 0 s (fun _ => 0) lam 0 0
  let g := Duality.g m
  have hB : q.rhoA < 1 := (le_max_left _ _).trans_lt q.rhoQ_lt_one
  have hphi (c : Spectral.Frequency) : f c =
      -(Complex.normSq (q.a (Waves.z 0 (Real.arccos c))) /
        (q.B^2*Complex.normSq (Waves.z 0 (Real.arccos c)))) *
      (polynomial s lam (Waves.z 0 (Real.arccos c))*q.b (Waves.z 0 (Real.arccos c))/
        q.a (Waves.z 0 (Real.arccos c))).re := by
    have h := upper_negative_actual q s lam 0 c (by simpa using hB)
    simpa only [mul_zero, Real.exp_zero, Real.sinh_zero, mul_one, mul_zero,
      Finset.sum_const_zero, neg_zero] using h
  have hc (c : Spectral.Frequency) : ‖Waves.z 0 (Real.arccos c)‖ = 1 := by
    have h := Waves.norm_z_pow 0 (Real.arccos c) 1
    simpa using h
  have hcoeff (c : Spectral.Frequency) : 0 <
      Complex.normSq (q.a (Waves.z 0 (Real.arccos c))) /
        (q.B^2*Complex.normSq (Waves.z 0 (Real.arccos c))) := by
    apply div_pos
    · exact Complex.normSq_pos.mpr (q.a_ne_zero_of_one_le_norm (hc c).ge)
    · exact mul_pos (sq_pos_of_pos q.B_pos) (Complex.normSq_pos.mpr (Waves.z_ne_zero _ _))
  have hfn : ∀ c, f c ≤ 0 := by
    intro c
    by_cases hc1 : c = oneFrequency
    · subst c
      rw [hphi, (unit_wave_eq_one_iff oneFrequency).2 rfl, polynomial_one]
      simp
    · rw [hphi]
      exact (mul_neg_of_neg_of_pos (neg_neg_of_pos (hcoeff c))
        (hcircle _ (hc c) (fun h => hc1 ((unit_wave_eq_one_iff c).1 h)))).le
  have hstrict : ∀ c, 0 ≤ g c → f c < 0 := by
    intro c hg
    have hc1 : c ≠ oneFrequency := by
      intro he; subst c; exact (g_one_negative q).not_ge hg
    rw [hphi]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos (hcoeff c))
      (hcircle _ (hc c) (fun h => hc1 ((unit_wave_eq_one_iff c).1 h)))
  obtain ⟨eta, heta, hnegative⟩ := balanced_perturbation f g
    (Duality.continuous_symbol _ _ _ _ _ _ _) (by unfold g Duality.g; fun_prop) hfn hstrict
  apply certificate_of_negative s (fun _ => 0) lam eta eta hs (fun _ _ => le_rfl)
    hlam heta.le heta.le
  · simp
  · intro c
    convert hnegative c using 1
    simp [f, g, Duality.symbol]
    ring

theorem upper_rate_lt_one (q : Tuning) (s : Finset ℕ) (lam : ℕ → ℝ)
    (hs : ∀ n ∈ s, 1 ≤ n) (hlam : ∀ n ∈ s, 0 ≤ lam n)
    (hmass : 0 < ∑ n ∈ s, lam n)
    (hcircle : ∀ z : ℂ, ‖z‖ = 1 → z ≠ 1 → 0 < (polynomial s lam z*q.b z/q.a z).re) :
    q.rate < 1 := by
  have hnonneg : ∀ z : ℂ, ‖z‖ = 1 → 0 ≤ (polynomial s lam z*q.b z/q.a z).re := by
    intro z hz
    by_cases hz1 : z = 1
    · simp [hz1]
    · exact (hcircle z hz hz1).le
  have hrate : q.rate < Real.exp 0 := by
    apply Growth.originalRate_lt_exp_of_certificates q.x_pos q.x_lt_y zero_lt_one q.beta_nonneg
    intro t ht
    rw [q.normalizedA_eq, q.normalizedB_eq]
    rcases ht.eq_or_lt with ht | ht
    · subst t; exact upper_zero_certificate q s lam hs hlam hcircle
    · exact upper_positive_certificate q s lam hs hlam hmass hnonneg ht
  simpa only [Real.exp_zero] using hrate

end
end polyak.General.Multipliers
