import polyak.General.Multipliers.Symbols
import polyak.General.Multipliers.Minimum
import polyak.General.Multipliers.Certificates
import polyak.Growth.SpectralUpper

/-! The disk part of the multiplier criterion.  The boundary sign is the
literal source ratio; all strict finite certificates are constructed. -/

namespace polyak.General.Multipliers
noncomputable section
open Set

theorem lower_disk_positive (q : Tuning) (s : Finset ℕ) (lam : ℕ → ℝ)
    (hs : ∀ n ∈ s, 1 ≤ n) (hmass : 0 < ∑ n ∈ s, lam n)
    (hcircle : ∀ z : ℂ, ‖z‖ = 1 → 0 ≤ (polynomial s lam z*q.a z/q.b z).re)
    {u : ℂ} (hu : ‖u‖ < 1) :
    0 < (polynomial s lam u*bSharp q u/aSharp q u).re := by
  apply real_pos_on_disk (F := fun u => polynomial s lam u*bSharp q u/aSharp q u)
  · constructor
    · apply DifferentiableOn.div
      · exact (differentiable_polynomial s lam).differentiableOn.mul (by unfold bSharp; fun_prop)
      · unfold aSharp; fun_prop
      · intro z hz; exact aSharp_ne_zero q (le_of_lt (by simpa using hz))
    · apply ContinuousOn.div
      · exact (differentiable_polynomial s lam).continuous.continuousOn.mul (by unfold bSharp; fun_prop)
      · unfold aSharp; fun_prop
      · intro z hz
        apply aSharp_ne_zero q
        have hsub := closure_minimal (show Metric.ball (0 : ℂ) 1 ⊆ Metric.closedBall 0 1 from
          Metric.ball_subset_closedBall) Metric.isClosed_closedBall hz
        simpa using hsub
  · intro z hz
    rw [sharp_ratio_re_circle q hz]
    exact mul_nonneg (div_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)) (hcircle z hz)
  · simpa only [polynomial_zero s lam hs, bSharp_zero, aSharp_zero,
      mul_one, div_one, Complex.ofReal_re] using hmass
  · exact hu

theorem lower_positive_certificate (q : Tuning) (s : Finset ℕ) (lam : ℕ → ℝ)
    (hs : ∀ n ∈ s, 1 ≤ n) (hlam : ∀ n ∈ s, 0 ≤ lam n)
    (hmass : 0 < ∑ n ∈ s, lam n)
    (hcircle : ∀ z : ℂ, ‖z‖ = 1 → 0 ≤ (polynomial s lam z*q.a z/q.b z).re)
    {t : ℝ} (ht : 0 < t) :
    Nonempty (Duality.StrictCertificate (Waves.multiplierMap q.A q.B q.beta t) t) := by
  apply certificate_of_negative s (fun n => lam n*Real.exp (-(n*t))) (fun _ => 0)
    0 (∑ n ∈ s, lam n*Real.exp (-(n*t))*Real.sinh (n*t)) hs
  · intro n hn; exact mul_nonneg (hlam n hn) (Real.exp_nonneg _)
  · intro _ _; exact le_rfl
  · exact le_rfl
  · apply Finset.sum_nonneg
    intro n hn
    apply mul_nonneg (mul_nonneg (hlam n hn) (Real.exp_nonneg _))
    exact Real.sinh_nonneg_iff.mpr (mul_nonneg (Nat.cast_nonneg n) ht.le)
  · exact lower_cancel_positive s lam t
  · intro c
    rw [lower_positive_actual q s lam ht.le]
    have hn := Waves.norm_z_pow (-t) (Real.arccos c) 1
    simp only [pow_one, Nat.cast_one, one_mul] at hn
    have hu : ‖Waves.z (-t) (Real.arccos c)‖ < 1 := by
      rw [hn, Real.exp_lt_one_iff]; exact neg_neg_of_pos ht
    have hpos := lower_disk_positive q s lam hs hmass hcircle hu
    have hcoeff : 0 < Complex.normSq (aSharp q (Waves.z (-t) (Real.arccos c))) /
        (q.B^2*Complex.normSq (Waves.z (-t) (Real.arccos c))) := by
      apply div_pos
      · exact Complex.normSq_pos.mpr (aSharp_ne_zero q hu.le)
      · exact mul_pos (sq_pos_of_pos q.B_pos) (Complex.normSq_pos.mpr (Waves.z_ne_zero _ _))
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hcoeff) hpos

theorem lower_rate_le_one (q : Tuning) (s : Finset ℕ) (lam : ℕ → ℝ)
    (hs : ∀ n ∈ s, 1 ≤ n) (hlam : ∀ n ∈ s, 0 ≤ lam n)
    (hmass : 0 < ∑ n ∈ s, lam n)
    (hcircle : ∀ z : ℂ, ‖z‖ = 1 → 0 ≤ (polynomial s lam z*q.a z/q.b z).re) :
    q.rate ≤ 1 := by
  by_contra h
  have hr : 1 < q.rate := lt_of_not_ge h
  have hlog : 0 < Real.log q.rate := Real.log_pos hr
  have hlt : q.rate < Real.exp (Real.log q.rate/2) := by
    apply Growth.originalRate_lt_exp_of_certificates q.x_pos q.x_lt_y zero_lt_one q.beta_nonneg
    intro t ht
    rw [q.normalizedA_eq, q.normalizedB_eq]
    exact lower_positive_certificate q s lam hs hlam hmass hcircle (lt_of_lt_of_le (half_pos hlog) ht)
  have he : Real.exp (Real.log q.rate/2) < q.rate := by
    conv_rhs => rw [← Real.exp_log (zero_lt_one.trans hr)]
    exact Real.exp_lt_exp.mpr (by linarith)
  exact (hlt.trans he).false

theorem upper_disk_positive (q : Tuning) (s : Finset ℕ) (lam : ℕ → ℝ)
    (hs : ∀ n ∈ s, 1 ≤ n) (hmass : 0 < ∑ n ∈ s, lam n)
    (hcircle : ∀ z : ℂ, ‖z‖ = 1 → 0 ≤ (polynomial s lam z*q.b z/q.a z).re)
    {u : ℂ} (hu : ‖u‖ < 1) :
    0 < (polynomial s lam u*aSharp q u/bSharp q u).re := by
  apply real_pos_on_disk (F := fun u => polynomial s lam u*aSharp q u/bSharp q u)
  · constructor
    · apply DifferentiableOn.div
      · exact (differentiable_polynomial s lam).differentiableOn.mul (by unfold aSharp; fun_prop)
      · unfold bSharp; fun_prop
      · intro z hz; exact bSharp_ne_zero q (le_of_lt (by simpa using hz))
    · apply ContinuousOn.div
      · exact (differentiable_polynomial s lam).continuous.continuousOn.mul (by unfold aSharp; fun_prop)
      · unfold bSharp; fun_prop
      · intro z hz
        apply bSharp_ne_zero q
        have hsub := closure_minimal (show Metric.ball (0 : ℂ) 1 ⊆ Metric.closedBall 0 1 from
          Metric.ball_subset_closedBall) Metric.isClosed_closedBall hz
        simpa using hsub
  · intro z hz
    rw [upper_sharp_ratio_re_circle q hz]
    exact mul_nonneg (div_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)) (hcircle z hz)
  · simpa only [polynomial_zero s lam hs, aSharp_zero, bSharp_zero,
      mul_one, div_one, Complex.ofReal_re] using hmass
  · exact hu

theorem upper_positive_certificate (q : Tuning) (s : Finset ℕ) (lam : ℕ → ℝ)
    (hs : ∀ n ∈ s, 1 ≤ n) (hlam : ∀ n ∈ s, 0 ≤ lam n)
    (hmass : 0 < ∑ n ∈ s, lam n)
    (hcircle : ∀ z : ℂ, ‖z‖ = 1 → 0 ≤ (polynomial s lam z*q.b z/q.a z).re)
    {t : ℝ} (ht : 0 < t) :
    Nonempty (Duality.StrictCertificate (Waves.multiplierMap q.A q.B q.beta t) t) := by
  apply certificate_of_negative s (fun _ => 0) (fun n => lam n*Real.exp (-(n*t)))
    (∑ n ∈ s, lam n*Real.exp (-(n*t))*Real.sinh (n*t)) 0 hs
  · intro _ _; exact le_rfl
  · intro n hn; exact mul_nonneg (hlam n hn) (Real.exp_nonneg _)
  · apply Finset.sum_nonneg
    intro n hn
    apply mul_nonneg (mul_nonneg (hlam n hn) (Real.exp_nonneg _))
    exact Real.sinh_nonneg_iff.mpr (mul_nonneg (Nat.cast_nonneg n) ht.le)
  · exact le_rfl
  · exact upper_cancel_positive s lam t
  · intro c
    rw [upper_positive_actual q s lam ht.le]
    have hn := Waves.norm_z_pow (-t) (Real.arccos c) 1
    simp only [pow_one, Nat.cast_one, one_mul] at hn
    have hu : ‖Waves.z (-t) (Real.arccos c)‖ < 1 := by
      rw [hn, Real.exp_lt_one_iff]; exact neg_neg_of_pos ht
    have hpos := upper_disk_positive q s lam hs hmass hcircle hu
    have hcoeff : 0 < Complex.normSq (bSharp q (Waves.z (-t) (Real.arccos c))) /
        (q.B^2*Complex.normSq (Waves.z (-t) (Real.arccos c))) := by
      apply div_pos
      · exact Complex.normSq_pos.mpr (bSharp_ne_zero q hu.le)
      · exact mul_pos (sq_pos_of_pos q.B_pos) (Complex.normSq_pos.mpr (Waves.z_ne_zero _ _))
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hcoeff) hpos

theorem upper_rate_le_one (q : Tuning) (s : Finset ℕ) (lam : ℕ → ℝ)
    (hs : ∀ n ∈ s, 1 ≤ n) (hlam : ∀ n ∈ s, 0 ≤ lam n)
    (hmass : 0 < ∑ n ∈ s, lam n)
    (hcircle : ∀ z : ℂ, ‖z‖ = 1 → 0 ≤ (polynomial s lam z*q.b z/q.a z).re) :
    q.rate ≤ 1 := by
  by_contra h
  have hr : 1 < q.rate := lt_of_not_ge h
  have hlog : 0 < Real.log q.rate := Real.log_pos hr
  have hlt : q.rate < Real.exp (Real.log q.rate/2) := by
    apply Growth.originalRate_lt_exp_of_certificates q.x_pos q.x_lt_y zero_lt_one q.beta_nonneg
    intro t ht
    rw [q.normalizedA_eq, q.normalizedB_eq]
    exact upper_positive_certificate q s lam hs hlam hmass hcircle (lt_of_lt_of_le (half_pos hlog) ht)
  have he : Real.exp (Real.log q.rate/2) < q.rate := by
    conv_rhs => rw [← Real.exp_log (zero_lt_one.trans hr)]
    exact Real.exp_lt_exp.mpr (by linarith)
  exact (hlt.trans he).false

end
end polyak.General.Multipliers
