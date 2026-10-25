import polyak.General.Multipliers.Pole
import polyak.Dynamics.Scale

/-! Source-facing endpoints for Appendix D and Theorem mult.  The rate
in the normalized source coordinates equals the original heavy-ball rate;
the multiplier hypotheses use nonnegative weights, not all zero. -/

namespace polyak.General.Multipliers
noncomputable section

theorem mass_pos_iff_not_all_zero (s : Finset ℕ) (lam : ℕ → ℝ)
    (hn : ∀ n ∈ s, 0 ≤ lam n) :
    0 < ∑ n ∈ s, lam n ↔ ∃ n ∈ s, lam n ≠ 0 := by
  rw [Finset.sum_pos_iff_of_nonneg hn]
  constructor
  · rintro ⟨n,hn,hpos⟩
    exact ⟨n,hn,ne_of_gt hpos⟩
  · rintro ⟨n,hs,hne⟩
    exact ⟨n,hs,lt_of_le_of_ne (hn n hs) hne.symm⟩

theorem original_rate_eq {mu L alpha beta : ℝ}
    (hmu : 0 < mu) (hL : mu < L) (ha : 0 < alpha)
    (hb : 0 ≤ beta) (hb1 : beta < 1) (hquad : alpha*L < 2*(1+beta)) :
    (Tuning.ofOriginal mu L alpha beta hmu hL ha hb hb1 hquad).rate =
      Dynamics.rate mu L alpha beta := by
  unfold Tuning.rate
  rw [Tuning.ofOriginal_x]
  have h := Dynamics.rate_scale (μ := mu) (L := L) (α := alpha) (β := beta) ha
  simpa only [Tuning.ofOriginal, div_self (ne_of_gt ha)] using h

theorem normSq_wave (t w : ℝ) : Complex.normSq (Waves.z t w) = Real.exp (2*t) := by
  simpa only [pow_one, Nat.cast_one, mul_one] using Waves.normSq_z_pow t w 1

theorem lower_positive_source_symbol (q : Tuning) (s : Finset ℕ) (lam : ℕ → ℝ)
    {t : ℝ} (ht : 0 ≤ t) (c : Spectral.Frequency) :
    Duality.symbol (Waves.multiplierMap q.A q.B q.beta t) t s
      (fun n => lam n*Real.exp (-(n*t))) (fun _ => 0) 0
      (∑ n ∈ s, lam n*Real.exp (-(n*t))*Real.sinh (n*t)) c =
      -(Real.exp (2*t)/q.B^2)*Complex.normSq (aSharp q (Waves.z (-t) (Real.arccos c))) *
      (polynomial s lam (Waves.z (-t) (Real.arccos c))*
        bSharp q (Waves.z (-t) (Real.arccos c))/
        aSharp q (Waves.z (-t) (Real.arccos c))).re := by
  rw [lower_positive_actual q s lam ht, normSq_wave]
  rw [show 2*(-t)=-(2*t) by ring, Real.exp_neg]
  field_simp

theorem upper_positive_source_symbol (q : Tuning) (s : Finset ℕ) (lam : ℕ → ℝ)
    {t : ℝ} (ht : 0 ≤ t) (c : Spectral.Frequency) :
    Duality.symbol (Waves.multiplierMap q.A q.B q.beta t) t s
      (fun _ => 0) (fun n => lam n*Real.exp (-(n*t)))
      (∑ n ∈ s, lam n*Real.exp (-(n*t))*Real.sinh (n*t)) 0 c =
      -(Real.exp (2*t)/q.B^2)*Complex.normSq (bSharp q (Waves.z (-t) (Real.arccos c))) *
      (polynomial s lam (Waves.z (-t) (Real.arccos c))*
        aSharp q (Waves.z (-t) (Real.arccos c))/
        bSharp q (Waves.z (-t) (Real.arccos c))).re := by
  rw [upper_positive_actual q s lam ht, normSq_wave]
  rw [show 2*(-t)=-(2*t) by ring, Real.exp_neg]
  field_simp

end
end polyak.General.Multipliers
