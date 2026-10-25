import polyak.General.Multipliers.Zero
import polyak.General.CubicSource

/-! Appendix D: the annulus part of the one-sided minimum principle and the
literal source-cubic bridge used by the rate regions. -/

namespace polyak.General.Multipliers
noncomputable section
open Set

def lowerRatio (q : Tuning) (s : Finset ℕ) (lam : ℕ → ℝ) (z : ℂ) : ℂ :=
  polynomial s lam z*q.a z/q.b z

theorem lowerRatio_diffContOnCl (q : Tuning) (s : Finset ℕ) (lam : ℕ → ℝ)
    {r : ℝ} (hr : q.rhoB < r) : DiffContOnCl ℂ (lowerRatio q s lam) (annulus r 1) := by
  constructor
  · apply DifferentiableOn.div
    · exact (differentiable_polynomial s lam).differentiableOn.mul (by unfold Tuning.a; fun_prop)
    · unfold Tuning.b; fun_prop
    · intro z hz; exact b_ne_zero_outside q (hr.trans hz.1)
  · apply ContinuousOn.div
    · exact (differentiable_polynomial s lam).continuous.continuousOn.mul (by unfold Tuning.a; fun_prop)
    · unfold Tuning.b; fun_prop
    · intro z hz; exact b_ne_zero_outside q (hr.trans_le (annulus_closure_subset _ _ hz).1)

theorem lower_annulus_nonnegative (q : Tuning) (s : Finset ℕ) (lam : ℕ → ℝ)
    {r : ℝ} (hr : q.rhoB < r)
    (hinner : ∀ z : ℂ, ‖z‖ = r → 0 ≤ (lowerRatio q s lam z).re)
    (houter : ∀ z : ℂ, ‖z‖ = 1 → 0 ≤ (lowerRatio q s lam z).re)
    {z : ℂ} (hz : z ∈ closure (annulus r 1)) : 0 ≤ (lowerRatio q s lam z).re :=
  real_nonneg_on_annulus (lowerRatio_diffContOnCl q s lam hr) hinner houter hz

theorem lower_annulus_positive (q : Tuning) (s : Finset ℕ) (lam : ℕ → ℝ)
    {r : ℝ} (hr : q.rhoB < r) (hr1 : r < 1)
    (hinner : ∀ z : ℂ, ‖z‖ = r → 0 ≤ (lowerRatio q s lam z).re)
    (houter : ∀ z : ℂ, ‖z‖ = 1 → z ≠ 1 → 0 < (lowerRatio q s lam z).re)
    {z : ℂ} (hz : z ∈ annulus r 1) : 0 < (lowerRatio q s lam z).re := by
  have hr0 : 0 < r := (rootRadius_nonneg _ _).trans_lt hr
  apply real_pos_on_annulus (F := lowerRatio q s lam) hr0 zero_lt_one
    (lowerRatio_diffContOnCl q s lam hr) hinner
  · intro w hw
    by_cases hw1 : w = 1
    · simp [lowerRatio, hw1]
    · exact (houter w hw hw1).le
  · refine ⟨-1, unit_mem_closure_annulus hr0 hr1 (by simp), houter (-1) (by simp) ?_⟩
    norm_num
  · exact hz

theorem lower_negative_certificate (q : Tuning) (s : Finset ℕ) (lam : ℕ → ℝ)
    (hs : ∀ n ∈ s, 1 ≤ n) (hlam : ∀ n ∈ s, 0 ≤ lam n)
    {r t : ℝ} (hr : q.rhoB < r) (hr1 : r < 1) (ht : t < 0)
    (htr : r < Real.exp t)
    (hinner : ∀ z : ℂ, ‖z‖ = r → 0 ≤ (lowerRatio q s lam z).re)
    (houter : ∀ z : ℂ, ‖z‖ = 1 → z ≠ 1 → 0 < (lowerRatio q s lam z).re) :
    Nonempty (Duality.StrictCertificate (Waves.multiplierMap q.A q.B q.beta t) t) := by
  apply certificate_of_negative s (fun n => lam n*Real.exp (n*t)) (fun _ => 0)
    (-(∑ n ∈ s, lam n*Real.exp (n*t)*Real.sinh (n*t))) 0 hs
  · intro n hn; exact mul_nonneg (hlam n hn) (Real.exp_nonneg _)
  · intro _ _; exact le_rfl
  · apply neg_nonneg.mpr
    apply Finset.sum_nonpos
    intro n hn
    apply mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (hlam n hn) (Real.exp_nonneg _))
    exact Real.sinh_nonpos_iff.mpr (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) ht.le)
  · exact le_rfl
  · exact lower_cancel_negative s lam t
  · intro c
    rw [lower_negative_actual q s lam t c (hr.trans htr)]
    have hn := Waves.norm_z_pow t (Real.arccos c) 1
    simp only [pow_one, Nat.cast_one, one_mul] at hn
    have hmem : Waves.z t (Real.arccos c) ∈ annulus r 1 := by
      change r < _ ∧ _ < 1
      rw [hn]
      exact ⟨htr, Real.exp_lt_one_iff.mpr ht⟩
    have hp := lower_annulus_positive q s lam hr hr1 hinner houter hmem
    have hc : 0 < Complex.normSq (q.b (Waves.z t (Real.arccos c))) /
        (q.B^2*Complex.normSq (Waves.z t (Real.arccos c))) := by
      apply div_pos
      · exact Complex.normSq_pos.mpr (b_ne_zero_outside q (hr.trans hmem.1))
      · exact mul_pos (sq_pos_of_pos q.B_pos) (Complex.normSq_pos.mpr (Waves.z_ne_zero _ _))
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hc) hp

theorem lower_rate_le_radius (q : Tuning) (s : Finset ℕ) (lam : ℕ → ℝ)
    (hs : ∀ n ∈ s, 1 ≤ n) (hlam : ∀ n ∈ s, 0 ≤ lam n)
    (hmass : 0 < ∑ n ∈ s, lam n)
    {r : ℝ} (hr : q.rhoB < r) (hr1 : r < 1)
    (hinner : ∀ z : ℂ, ‖z‖ = r → 0 ≤ (lowerRatio q s lam z).re)
    (houter : ∀ z : ℂ, ‖z‖ = 1 → z ≠ 1 → 0 < (lowerRatio q s lam z).re) :
    q.rate ≤ r := by
  have hr0 : 0 < r := (rootRadius_nonneg _ _).trans_lt hr
  have hnonneg : ∀ z : ℂ, ‖z‖ = 1 → 0 ≤ (lowerRatio q s lam z).re := by
    intro z hz
    by_cases hz1 : z = 1
    · simp [lowerRatio, hz1]
    · exact (houter z hz hz1).le
  have hstrict : q.rate < 1 := lower_rate_lt_one q s lam hs hlam hmass houter
  by_contra h
  have hrate : r < q.rate := lt_of_not_ge h
  let t0 := (Real.log r+Real.log q.rate)/2
  have hlog : Real.log r < Real.log q.rate := Real.log_lt_log hr0 hrate
  have ht0 : Real.log r < t0 := by dsimp [t0]; linarith
  have hlt : q.rate < Real.exp t0 := by
    apply Growth.originalRate_lt_exp_of_certificates q.x_pos q.x_lt_y zero_lt_one q.beta_nonneg
    intro t ht
    rw [q.normalizedA_eq, q.normalizedB_eq]
    rcases lt_trichotomy t 0 with htneg | htzero | htpos
    · apply lower_negative_certificate q s lam hs hlam hr hr1 htneg
      · have := Real.exp_lt_exp.mpr (ht0.trans_le ht)
        simpa only [Real.exp_log hr0] using this
      · exact hinner
      · exact houter
    · subst t; exact lower_zero_certificate q s lam hs hlam houter
    · exact lower_positive_certificate q s lam hs hlam hmass hnonneg htpos
  have he : Real.exp t0 < q.rate := by
    conv_rhs => rw [← Real.exp_log (hr0.trans hrate)]
    exact Real.exp_lt_exp.mpr (by dsimp [t0]; linarith)
  exact (hlt.trans he).false

def upperRatio (q : Tuning) (s : Finset ℕ) (lam : ℕ → ℝ) (z : ℂ) : ℂ :=
  polynomial s lam z*q.b z/q.a z

theorem upperRatio_diffContOnCl (q : Tuning) (s : Finset ℕ) (lam : ℕ → ℝ)
    {r : ℝ} (hr : q.rhoA < r) : DiffContOnCl ℂ (upperRatio q s lam) (annulus r 1) := by
  constructor
  · apply DifferentiableOn.div
    · exact (differentiable_polynomial s lam).differentiableOn.mul (by unfold Tuning.b; fun_prop)
    · unfold Tuning.a; fun_prop
    · intro z hz; exact a_ne_zero_outside q (hr.trans hz.1)
  · apply ContinuousOn.div
    · exact (differentiable_polynomial s lam).continuous.continuousOn.mul (by unfold Tuning.b; fun_prop)
    · unfold Tuning.a; fun_prop
    · intro z hz; exact a_ne_zero_outside q (hr.trans_le (annulus_closure_subset _ _ hz).1)

theorem upper_annulus_nonnegative (q : Tuning) (s : Finset ℕ) (lam : ℕ → ℝ)
    {r : ℝ} (hr : q.rhoA < r)
    (hinner : ∀ z : ℂ, ‖z‖ = r → 0 ≤ (upperRatio q s lam z).re)
    (houter : ∀ z : ℂ, ‖z‖ = 1 → 0 ≤ (upperRatio q s lam z).re)
    {z : ℂ} (hz : z ∈ closure (annulus r 1)) : 0 ≤ (upperRatio q s lam z).re :=
  real_nonneg_on_annulus (upperRatio_diffContOnCl q s lam hr) hinner houter hz

theorem upper_annulus_positive (q : Tuning) (s : Finset ℕ) (lam : ℕ → ℝ)
    {r : ℝ} (hr : q.rhoA < r) (hr1 : r < 1)
    (hinner : ∀ z : ℂ, ‖z‖ = r → 0 ≤ (upperRatio q s lam z).re)
    (houter : ∀ z : ℂ, ‖z‖ = 1 → z ≠ 1 → 0 < (upperRatio q s lam z).re)
    {z : ℂ} (hz : z ∈ annulus r 1) : 0 < (upperRatio q s lam z).re := by
  have hr0 : 0 < r := (rootRadius_nonneg _ _).trans_lt hr
  apply real_pos_on_annulus (F := upperRatio q s lam) hr0 zero_lt_one
    (upperRatio_diffContOnCl q s lam hr) hinner
  · intro w hw
    by_cases hw1 : w = 1
    · simp [upperRatio, hw1]
    · exact (houter w hw hw1).le
  · refine ⟨-1, unit_mem_closure_annulus hr0 hr1 (by simp), houter (-1) (by simp) ?_⟩
    norm_num
  · exact hz

theorem upper_negative_certificate (q : Tuning) (s : Finset ℕ) (lam : ℕ → ℝ)
    (hs : ∀ n ∈ s, 1 ≤ n) (hlam : ∀ n ∈ s, 0 ≤ lam n)
    {r t : ℝ} (hr : q.rhoA < r) (hr1 : r < 1) (ht : t < 0)
    (htr : r < Real.exp t)
    (hinner : ∀ z : ℂ, ‖z‖ = r → 0 ≤ (upperRatio q s lam z).re)
    (houter : ∀ z : ℂ, ‖z‖ = 1 → z ≠ 1 → 0 < (upperRatio q s lam z).re) :
    Nonempty (Duality.StrictCertificate (Waves.multiplierMap q.A q.B q.beta t) t) := by
  apply certificate_of_negative s (fun _ => 0) (fun n => lam n*Real.exp (n*t))
    0 (-(∑ n ∈ s, lam n*Real.exp (n*t)*Real.sinh (n*t))) hs
  · intro _ _; exact le_rfl
  · intro n hn; exact mul_nonneg (hlam n hn) (Real.exp_nonneg _)
  · exact le_rfl
  · apply neg_nonneg.mpr
    apply Finset.sum_nonpos
    intro n hn
    apply mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (hlam n hn) (Real.exp_nonneg _))
    exact Real.sinh_nonpos_iff.mpr (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) ht.le)
  · exact upper_cancel_negative s lam t
  · intro c
    rw [upper_negative_actual q s lam t c (hr.trans htr)]
    have hn := Waves.norm_z_pow t (Real.arccos c) 1
    simp only [pow_one, Nat.cast_one, one_mul] at hn
    have hmem : Waves.z t (Real.arccos c) ∈ annulus r 1 := by
      change r < _ ∧ _ < 1
      rw [hn]
      exact ⟨htr, Real.exp_lt_one_iff.mpr ht⟩
    have hp := upper_annulus_positive q s lam hr hr1 hinner houter hmem
    have hc : 0 < Complex.normSq (q.a (Waves.z t (Real.arccos c))) /
        (q.B^2*Complex.normSq (Waves.z t (Real.arccos c))) := by
      apply div_pos
      · exact Complex.normSq_pos.mpr (a_ne_zero_outside q (hr.trans hmem.1))
      · exact mul_pos (sq_pos_of_pos q.B_pos) (Complex.normSq_pos.mpr (Waves.z_ne_zero _ _))
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hc) hp

theorem upper_rate_le_radius (q : Tuning) (s : Finset ℕ) (lam : ℕ → ℝ)
    (hs : ∀ n ∈ s, 1 ≤ n) (hlam : ∀ n ∈ s, 0 ≤ lam n)
    (hmass : 0 < ∑ n ∈ s, lam n)
    {r : ℝ} (hr : q.rhoA < r) (hr1 : r < 1)
    (hinner : ∀ z : ℂ, ‖z‖ = r → 0 ≤ (upperRatio q s lam z).re)
    (houter : ∀ z : ℂ, ‖z‖ = 1 → z ≠ 1 → 0 < (upperRatio q s lam z).re) :
    q.rate ≤ r := by
  have hr0 : 0 < r := (rootRadius_nonneg _ _).trans_lt hr
  have hnonneg : ∀ z : ℂ, ‖z‖ = 1 → 0 ≤ (upperRatio q s lam z).re := by
    intro z hz
    by_cases hz1 : z = 1
    · simp [upperRatio, hz1]
    · exact (houter z hz hz1).le
  have hstrict : q.rate < 1 := upper_rate_lt_one q s lam hs hlam hmass houter
  by_contra h
  have hrate : r < q.rate := lt_of_not_ge h
  let t0 := (Real.log r+Real.log q.rate)/2
  have hlog : Real.log r < Real.log q.rate := Real.log_lt_log hr0 hrate
  have ht0 : Real.log r < t0 := by dsimp [t0]; linarith
  have hlt : q.rate < Real.exp t0 := by
    apply Growth.originalRate_lt_exp_of_certificates q.x_pos q.x_lt_y zero_lt_one q.beta_nonneg
    intro t ht
    rw [q.normalizedA_eq, q.normalizedB_eq]
    rcases lt_trichotomy t 0 with htneg | htzero | htpos
    · apply upper_negative_certificate q s lam hs hlam hr hr1 htneg
      · have := Real.exp_lt_exp.mpr (ht0.trans_le ht)
        simpa only [Real.exp_log hr0] using this
      · exact hinner
      · exact houter
    · subst t; exact upper_zero_certificate q s lam hs hlam houter
    · exact upper_positive_certificate q s lam hs hlam hmass hnonneg htpos
  have he : Real.exp t0 < q.rate := by
    conv_rhs => rw [← Real.exp_log (hr0.trans hrate)]
    exact Real.exp_lt_exp.mpr (by dsimp [t0]; linarith)
  exact (hlt.trans he).false

end
end polyak.General.Multipliers
