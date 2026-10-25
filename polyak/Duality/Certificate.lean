import polyak.Spectral.GeneralCompact

/-!
Article: (strictcert) and spectralgeneral(a), the certificate direction.
Use: finite nonnegative combinations of actual spectral interpolation slacks.
Proof: probability integration and exact cancellation of the common value constant.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace polyak.Duality

open Spectral

/-- Article: g. Use: minimizer slack of an arbitrary continuous multiplier. -/
def g (m : C(Frequency, ℂ)) (c : Frequency) : ℝ := 1 - Complex.normSq (m c)

/-- Article: aₙ. Use: symmetric spectral lag slack. -/
def a (m : C(Frequency, ℂ)) (t : ℝ) (n : ℕ) (c : Frequency) : ℝ :=
  g m c * (Real.cosh (n * t) - Real.cos (n * Real.arccos c))

/-- Article: bₙ. Use: skew spectral lag slack. -/
def b (m : C(Frequency, ℂ)) (n : ℕ) (c : Frequency) : ℝ :=
  2 * (m c).im * Real.sin (n * Real.arccos c)

/-- Article: Φₜ. Use: the actual frequency symbol of the finite certificate. -/
def symbol (m : C(Frequency, ℂ)) (t : ℝ) (lags : Finset ℕ)
    (α β : ℕ → ℝ) (γplus γminus : ℝ) (c : Frequency) : ℝ :=
  (∑ n ∈ lags, (α n * (a m t n c - b m n c) + β n * (a m t n c + b m n c))) +
    (γplus + γminus) * g m c

/-- Article: strictcert. Use: finite, strictly negative, C-free spectral certificate. -/
structure StrictCertificate (m : C(Frequency, ℂ)) (t : ℝ) where
  /-- Article: finite lag support. -/
  lags : Finset ℕ
  /-- Article: only positive lags are interpolation constraints. -/
  positive_lag : ∀ n ∈ lags, 1 ≤ n
  /-- Article: lower lag weights. -/
  α : ℕ → ℝ
  /-- Article: upper lag weights. -/
  β : ℕ → ℝ
  /-- Article: nonnegative lower weights. -/
  α_nonneg : ∀ n ∈ lags, 0 ≤ α n
  /-- Article: nonnegative upper weights. -/
  β_nonneg : ∀ n ∈ lags, 0 ≤ β n
  /-- Article: positive minimizer slack weight. -/
  γplus : ℝ
  /-- Article: negative minimizer slack weight. -/
  γminus : ℝ
  /-- Article: nonnegative minimizer multiplier. -/
  γplus_nonneg : 0 ≤ γplus
  /-- Article: nonnegative minimizer multiplier. -/
  γminus_nonneg : 0 ≤ γminus
  /-- Article: strict separation margin. -/
  ε : ℝ
  /-- Article: positive strict margin. -/
  ε_pos : 0 < ε
  /-- Article: the coefficient of the common value constant is zero. -/
  cancel : (∑ n ∈ lags, (α n - β n) * Real.sinh (n * t)) + γplus - γminus = 0
  /-- Article: pointwise strict negativity on the entire compact frequency interval. -/
  strict : ∀ c, symbol m t lags α β γplus γminus c ≤ -ε

/-- Article: continuity of the complete symbol. Proof: finite algebra of continuous functions. -/
theorem continuous_symbol (m : C(Frequency, ℂ)) (t : ℝ) (lags : Finset ℕ)
    (α β : ℕ → ℝ) (γplus γminus : ℝ) :
    Continuous (symbol m t lags α β γplus γminus) := by
  unfold symbol a b g
  fun_prop

/-- Article: integration of the certificate symbol. Proof: linearity for finite continuous sums. -/
theorem integral_symbol (ν : Spectrum) (m : C(Frequency, ℂ)) (t : ℝ) (lags : Finset ℕ)
    (α β : ℕ → ℝ) (γplus γminus : ℝ) :
    (∫ c, symbol m t lags α β γplus γminus c ∂ν) =
      (∑ n ∈ lags, (α n * (Waves.spectrumA ν m t n - Waves.spectrumB ν m n) +
        β n * (Waves.spectrumA ν m t n + Waves.spectrumB ν m n))) +
        (γplus + γminus) * Waves.spectrumG ν m := by
  have ha (n : ℕ) : Integrable (a m t n) (ν : Measure Frequency) :=
    integrable_continuous ν (by unfold a g; fun_prop)
  have hb (n : ℕ) : Integrable (b m n) (ν : Measure Frequency) :=
    integrable_continuous ν (by unfold b; fun_prop)
  have hg : Integrable (g m) (ν : Measure Frequency) :=
    integrable_continuous ν (by unfold g; fun_prop)
  have hsum : Integrable (fun c => ∑ n ∈ lags,
      (α n * (a m t n c - b m n c) + β n * (a m t n c + b m n c)))
      (ν : Measure Frequency) := integrable_continuous ν (by unfold a b g; fun_prop)
  unfold symbol
  rw [integral_add hsum (hg.const_mul _), integral_finsetSum]
  · congr 1
    · apply Finset.sum_congr rfl
      intro n _
      have ha' := ha n
      have hb' := hb n
      rw [integral_add (integrable_continuous ν (by unfold a b g; fun_prop) : Integrable (fun c => α n * (a m t n c - b m n c))
          (ν : Measure Frequency)) (integrable_continuous ν (by unfold a b g; fun_prop) : Integrable
          (fun c => β n * (a m t n c + b m n c)) (ν : Measure Frequency))]
      rw [integral_const_mul, integral_const_mul, integral_sub ha' hb', integral_add ha' hb']
      rfl
    · rw [integral_const_mul]
      rfl
  · intro n _
    exact integrable_continuous ν (by unfold a b g; fun_prop)

/-- Article: exact cancellation of C after integration. Proof: the charge equation. -/
theorem StrictCertificate.integral_eq_slacks {m : C(Frequency, ℂ)} {t : ℝ}
    (cert : StrictCertificate m t) (ν : Spectrum) (C : ℝ) :
    (∫ c, symbol m t cert.lags cert.α cert.β cert.γplus cert.γminus c ∂ν) =
      (∑ n ∈ cert.lags,
        (cert.α n * (Waves.spectrumA ν m t n - Waves.spectrumB ν m n +
          C * Real.sinh (n * t)) +
        cert.β n * (Waves.spectrumA ν m t n + Waves.spectrumB ν m n -
          C * Real.sinh (n * t)))) +
      cert.γplus * (Waves.spectrumG ν m + C) +
      cert.γminus * (Waves.spectrumG ν m - C) := by
  rw [integral_symbol]
  have hx : (∑ n ∈ cert.lags,
      (cert.α n * (Waves.spectrumA ν m t n - Waves.spectrumB ν m n + C * Real.sinh (n * t)) +
      cert.β n * (Waves.spectrumA ν m t n + Waves.spectrumB ν m n - C * Real.sinh (n * t)))) =
      (∑ n ∈ cert.lags,
        (cert.α n * (Waves.spectrumA ν m t n - Waves.spectrumB ν m n) +
        cert.β n * (Waves.spectrumA ν m t n + Waves.spectrumB ν m n))) +
      C * ∑ n ∈ cert.lags, (cert.α n - cert.β n) * Real.sinh (n * t) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hx]
  have hm := congrArg (fun x : ℝ => C * x) cert.cancel
  nlinarith [hm]

/-- Article: a strict certificate excludes every feasible spectrum.
Proof: nonnegative weighted slacks have integral at most the negative margin. -/
theorem StrictCertificate.not_feasible {m : C(Frequency, ℂ)} {t : ℝ}
    (cert : StrictCertificate m t) (ν : Spectrum) (C : ℝ) :
    ¬ Waves.MixtureFeasible ν m C t := by
  intro h
  have hsum : 0 ≤ (∫ c, symbol m t cert.lags cert.α cert.β cert.γplus cert.γminus c ∂ν) := by
    rw [cert.integral_eq_slacks ν C]
    have hstar := abs_le.mp h.1
    apply add_nonneg
    · apply add_nonneg
      · apply Finset.sum_nonneg
        intro n hn
        exact add_nonneg (mul_nonneg (cert.α_nonneg n hn)
          (h.2 n (cert.positive_lag n hn)).1)
          (mul_nonneg (cert.β_nonneg n hn) (h.2 n (cert.positive_lag n hn)).2)
      · exact mul_nonneg cert.γplus_nonneg (by linarith [hstar.1])
    · exact mul_nonneg cert.γminus_nonneg (by linarith [hstar.2])
  have hle := integral_mono (integrable_continuous ν (continuous_symbol _ _ _ _ _ _ _))
    (integrable_const (-cert.ε)) cert.strict
  have hnegative : (∫ c, symbol m t cert.lags cert.α cert.β cert.γplus cert.γminus c ∂ν) ≤
      -cert.ε := by simpa using hle
  linarith [cert.ε_pos]

end polyak.Duality
