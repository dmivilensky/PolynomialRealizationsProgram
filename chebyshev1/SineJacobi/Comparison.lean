import chebyshev1.SineJacobi.GainAsymptotics
import chebyshev1.SineJacobi.EnergyBound
import chebyshev1.Prefix.Asymptotics

/-!
Article: chebyshev1, Theorem 5.2.
The strict asymptotic improvement stated after Theorem 5.2.
Result: `chebyshev1.SineJacobi.gain_eventually_lt_prefix` supplies the stated article
conclusion.
-/
namespace chebyshev1.SineJacobi
noncomputable section
open Real Filter Topology
open scoped Asymptotics

/--
The stated quantitative bound `(fun N : ℕ => ((data N).realization I).gain I N) ~[atTop] (fun N
: ℕ => (2*sqrt sineEnergy/I.delta)*(N:ℝ)^(3/2:ℝ)*I.epsilon N)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev1, Theorem 5.2.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.gain_asymptotic_ratio` with the
arguments shown in the proof.
-/
theorem gain_isEquivalent (I : SpectralInterval) :
    (fun N : ℕ => ((data N).realization I).gain I N) ~[atTop]
      (fun N : ℕ => (2*sqrt sineEnergy/I.delta)*(N:ℝ)^(3/2:ℝ)*I.epsilon N) :=
  Asymptotics.isEquivalent_of_tendsto_one (gain_asymptotic_ratio I)

/--
The stated quantitative bound `2*sqrt sineEnergy < 4/sqrt 3`.

Use: `chebyshev1.SineJacobi.gain_eventually_lt_prefix` uses this bound to establish
establishes the stated eventual or almost-everywhere assertion `∀ᶠ N : ℕ in atTop, ((data
N).realization I).gain I N < (Prefix.realization I).gain I N`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.gain_eventually_lt_prefix`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.sineEnergy_ge_one`,
`chebyshev1.SineJacobi.sineEnergy_lt_four_thirds` with the arguments shown in the proof.
-/
theorem leading_constant_lt_prefix : 2*sqrt sineEnergy < 4/sqrt 3 := by
  -- Use the identities/estimates `chebyshev1.SineJacobi.sineEnergy_ge_one`,
  -- `chebyshev1.SineJacobi.sineEnergy_lt_four_thirds` with the arguments shown in the
  -- proof.
  have h := sqrt_lt_sqrt (show 0 ≤ sineEnergy by linarith [sineEnergy_ge_one])
    sineEnergy_lt_four_thirds
  have he : 2*sqrt (4/3:ℝ) = 4/sqrt 3 := by
    rw [sqrt_div (by norm_num : (0:ℝ) ≤ 4)]
    norm_num
    ring
  rw [← he]
  linarith

/--
The strict asymptotic improvement stated after Theorem 5.2.

Establishes the stated eventual or almost-everywhere assertion `∀ᶠ N : ℕ in atTop, ((data
N).realization I).gain I N < (Prefix.realization I).gain I N`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev1, Theorem 5.2.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Prove equality of functions by evaluating both
sides at an arbitrary argument.
-/
theorem gain_eventually_lt_prefix (I : SpectralInterval) :
    ∀ᶠ N : ℕ in atTop, ((data N).realization I).gain I N < (Prefix.realization I).gain I N := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hs := (gain_asymptotic_ratio I).const_mul (2*sqrt sineEnergy)
  simp only [mul_one] at hs
  have hp := Prefix.gain_asymptotic I
  have hc := leading_constant_lt_prefix
  have he : ∀ᶠ N : ℕ in atTop,
      ((data N).realization I).gain I N * I.delta /
        (I.epsilon N*(N:ℝ)*sqrt (N:ℝ)) <
      (Prefix.realization I).gain I N * I.delta /
        (I.epsilon N*(N:ℝ)*sqrt (N:ℝ)) := by
    -- Record the convergence hs with its source filter and target limit before taking limits
    -- in the subsequent identities/bounds.
    have hs' : Tendsto (fun N : ℕ => ((data N).realization I).gain I N * I.delta /
        (I.epsilon N*(N:ℝ)*sqrt (N:ℝ))) atTop (𝓝 (2*sqrt sineEnergy)) := by
      convert hs using 1
      funext N
      have hpow : (N:ℝ)^(3/2:ℝ) = (N:ℝ)*sqrt (N:ℝ) := by
        rw [show (3/2:ℝ) = 1+1/2 by norm_num,
          rpow_add_of_nonneg (Nat.cast_nonneg N) (by norm_num) (by norm_num), rpow_one,
          ← sqrt_eq_rpow]
      rw [hpow]
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      have hc : sqrt sineEnergy * (sqrt sineEnergy)⁻¹ = 1 :=
        mul_inv_cancel₀ (sqrt_pos.mpr sineEnergy_pos).ne'
      linear_combination -((data N).realization I).gain I N*I.delta*
        (sqrt (N:ℝ))⁻¹*(N:ℝ)⁻¹*(I.epsilon N)⁻¹*hc
    exact hs'.eventually_lt hp hc
  filter_upwards [he, eventually_gt_atTop 0] with N hn hN
  have hNr : 0 < (N:ℝ) := by exact_mod_cast hN
  have hd : 0 < I.epsilon N*(N:ℝ)*sqrt (N:ℝ) := by
    exact mul_pos (mul_pos (one_div_pos.mpr (I.den_pos N)) hNr) (sqrt_pos.mpr hNr)
  have hm := (div_lt_div_iff_of_pos_right hd).mp hn
  nlinarith [I.delta_pos]

end
end chebyshev1.SineJacobi
