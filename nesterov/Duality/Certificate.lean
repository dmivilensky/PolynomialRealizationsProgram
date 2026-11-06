import nesterov.Spectral.Feasibility

/-!
Article: (strictcert) and spectralgeneral(a), the certificate direction.
Use: finite nonnegative combinations of actual spectral interpolation slacks.
Proof: probability integration and exact cancellation of the common value constant.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace nesterov.Duality

open Spectral

/-- Article: Φₜ. Use: the actual frequency symbol of the finite certificate. -/
def symbol (m : SymbolPair) (t : ℝ) (lags : Finset ℕ)
    (α β : ℕ → ℝ) (γplus γminus : ℝ) (c : Frequency) : ℝ :=
  (∑ n ∈ lags, (α n * (lagA m t n c - lagB m n c) + β n * (lagA m t n c + lagB m n c))) +
    (γplus + γminus) * g m c

/-- Article: strictcert. Use: finite, strictly negative, C-free spectral certificate. -/
structure StrictCertificate (m : SymbolPair) (t : ℝ) where
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
theorem continuous_symbol (m : SymbolPair) (t : ℝ) (lags : Finset ℕ)
    (α β : ℕ → ℝ) (γplus γminus : ℝ) :
    Continuous (symbol m t lags α β γplus γminus) := by
  unfold symbol lagA lagB g skew
  fun_prop

/-- Article: integration of the certificate symbol. Proof: linearity for finite continuous sums. -/
theorem integral_symbol (ν : Spectrum) (m : SymbolPair) (t : ℝ) (lags : Finset ℕ)
    (α β : ℕ → ℝ) (γplus γminus : ℝ) :
    (∫ c, symbol m t lags α β γplus γminus c ∂ν) =
      (∑ n ∈ lags, (α n * (meanA ν m t n - meanB ν m n) +
        β n * (meanA ν m t n + meanB ν m n))) +
        (γplus + γminus) * meanG ν m := by
  have ha (n : ℕ) : Integrable (lagA m t n) (ν : Measure Frequency) :=
    polyak.Spectral.integrable_continuous ν (by unfold lagA g; fun_prop)
  have hb (n : ℕ) : Integrable (lagB m n) (ν : Measure Frequency) :=
    polyak.Spectral.integrable_continuous ν (by unfold lagB skew; fun_prop)
  have hg : Integrable (g m) (ν : Measure Frequency) :=
    polyak.Spectral.integrable_continuous ν (by unfold g; fun_prop)
  have hsum : Integrable (fun c => ∑ n ∈ lags,
      (α n * (lagA m t n c - lagB m n c) + β n * (lagA m t n c + lagB m n c)))
      (ν : Measure Frequency) := polyak.Spectral.integrable_continuous ν (by unfold lagA lagB g skew; fun_prop)
  unfold symbol
  rw [integral_add hsum (hg.const_mul _), integral_finsetSum]
  · congr 1
    · apply Finset.sum_congr rfl
      intro n _
      have ha' := ha n
      have hb' := hb n
      rw [integral_add (polyak.Spectral.integrable_continuous ν (by unfold lagA lagB g skew; fun_prop) : Integrable (fun c => α n * (lagA m t n c - lagB m n c))
          (ν : Measure Frequency)) (polyak.Spectral.integrable_continuous ν (by unfold lagA lagB g skew; fun_prop) : Integrable
          (fun c => β n * (lagA m t n c + lagB m n c)) (ν : Measure Frequency))]
      rw [integral_const_mul, integral_const_mul, integral_sub ha' hb', integral_add ha' hb']
      rfl
    · rw [integral_const_mul]
      rfl
  · intro n _
    exact polyak.Spectral.integrable_continuous ν (by unfold lagA lagB g skew; fun_prop)

/-- Article: exact cancellation of C after integration. Proof: the charge equation. -/
theorem StrictCertificate.integral_eq_slacks {m : SymbolPair} {t : ℝ}
    (cert : StrictCertificate m t) (ν : Spectrum) (C : ℝ) :
    (∫ c, symbol m t cert.lags cert.α cert.β cert.γplus cert.γminus c ∂ν) =
      (∑ n ∈ cert.lags,
        (cert.α n * (meanA ν m t n - meanB ν m n +
          C * Real.sinh (n * t)) +
        cert.β n * (meanA ν m t n + meanB ν m n -
          C * Real.sinh (n * t)))) +
      cert.γplus * (meanG ν m + C) +
      cert.γminus * (meanG ν m - C) := by
  rw [integral_symbol]
  have hx : (∑ n ∈ cert.lags,
      (cert.α n * (meanA ν m t n - meanB ν m n + C * Real.sinh (n * t)) +
      cert.β n * (meanA ν m t n + meanB ν m n - C * Real.sinh (n * t)))) =
      (∑ n ∈ cert.lags,
        (cert.α n * (meanA ν m t n - meanB ν m n) +
        cert.β n * (meanA ν m t n + meanB ν m n))) +
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
theorem StrictCertificate.not_feasible {m : SymbolPair} {t : ℝ}
    (cert : StrictCertificate m t) (ν : Spectrum) (C : ℝ) :
    ¬ Feasible m t ν C := by
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
  have hle := integral_mono (polyak.Spectral.integrable_continuous ν (continuous_symbol _ _ _ _ _ _ _))
    (integrable_const (-cert.ε)) cert.strict
  have hnegative : (∫ c, symbol m t cert.lags cert.α cert.β cert.γplus cert.γminus c ∂ν) ≤
      -cert.ε := by simpa using hle
  linarith [cert.ε_pos]

end nesterov.Duality

namespace nesterov.Spectral

/-- The finite strict alternative for the two-amplitude program. -/
abbrev StrictCertificate := nesterov.Duality.StrictCertificate

end nesterov.Spectral
