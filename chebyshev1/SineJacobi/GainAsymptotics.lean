import chebyshev1.SineJacobi.ProfileEnergy
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
Article: chebyshev1, Theorem 5.2.
Theorem 5.2: the ratio to the stated N^(3/2) leading term tends to one.
Use: `chebyshev1.SineJacobi.gain_asymptotic_ratio` feeds
`chebyshev1.SineJacobi.gain_eventually_lt_prefix` (The strict asymptotic improvement stated
after Theorem 5.2).
Proof chain: `chebyshev1.SineJacobi.gain_isEquivalent` — chebyshev1, Theorem 5.2; Exact sine
gain, resolvent expression, asymptotics and energy value.
-/
namespace chebyshev1.SineJacobi
noncomputable section
open Real Filter Topology
open scoped BigOperators

/--
The stated quantitative bound `0 < sineEnergy`.

Use: `chebyshev1.SineJacobi.gain_asymptotic_ratio` uses this bound to establish convergence
along the specified source filter to the specified limit: `Tendsto (fun N : ℕ => ((data
N).realization I).gain I N/ ((2*sqrt sineEnergy/I.delta)*(N:ℝ)^(3/2:ℝ)*I.epsilon N)) atTop (𝓝
1)`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.gain_eventually_lt_prefix`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.sineEnergy_ge_one` with the
arguments shown in the proof.
-/
theorem sineEnergy_pos : 0 < sineEnergy := lt_of_lt_of_le (by norm_num) sineEnergy_ge_one

/--
Exact identity `sqrt ((N:ℝ)^3) = (N:ℝ)*sqrt (N:ℝ)`.

Use: `chebyshev1.SineJacobi.gain_asymptotic_ratio` rewrites with this identity to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun N : ℕ =>
((data N).realization I).gain I N/ ((2*sqrt sineEnergy/I.delta)*(N:ℝ)^(3/2:ℝ)*I.epsilon N))
atTop (𝓝 1)`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.gain_isEquivalent`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
private theorem sqrt_cube (N : ℕ) : sqrt ((N:ℝ)^3) = (N:ℝ)*sqrt (N:ℝ) := by
  rw [show (N:ℝ)^3 = (N:ℝ)^2*(N:ℝ) by ring, sqrt_mul (sq_nonneg _),
    sqrt_sq (Nat.cast_nonneg N)]

/--
Exact identity `(N:ℝ)^(3/2:ℝ) = (N:ℝ)*sqrt (N:ℝ)`.

Use: `chebyshev1.SineJacobi.gain_asymptotic_ratio` rewrites with this identity to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun N : ℕ =>
((data N).realization I).gain I N/ ((2*sqrt sineEnergy/I.delta)*(N:ℝ)^(3/2:ℝ)*I.epsilon N))
atTop (𝓝 1)`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.gain_isEquivalent`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
private theorem rpow_three_halves (N : ℕ) : (N:ℝ)^(3/2:ℝ) = (N:ℝ)*sqrt (N:ℝ) := by
  rw [show (3/2:ℝ) = 1+1/2 by norm_num,
    rpow_add_of_nonneg (Nat.cast_nonneg N) (by norm_num) (by norm_num), rpow_one,
    ← sqrt_eq_rpow]

/--
Theorem 5.2: the ratio to the stated N^(3/2) leading term tends to one.

Convergence along the specified source filter to the specified limit: `Tendsto (fun N : ℕ =>
((data N).realization I).gain I N/ ((2*sqrt sineEnergy/I.delta)*(N:ℝ)^(3/2:ℝ)*I.epsilon N))
atTop (𝓝 1)`.

Use: `chebyshev1.SineJacobi.gain_eventually_lt_prefix` uses this limit to establish
establishes the stated eventual or almost-everywhere assertion `∀ᶠ N : ℕ in atTop, ((data
N).realization I).gain I N < (Prefix.realization I).gain I N`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.gain_isEquivalent`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Clear the denominators using the available nonzero
hypotheses, then verify the remaining algebraic identity.
-/
theorem gain_asymptotic_ratio (I : SpectralInterval) :
    Tendsto (fun N : ℕ => ((data N).realization I).gain I N/
      ((2*sqrt sineEnergy/I.delta)*(N:ℝ)^(3/2:ℝ)*I.epsilon N)) atTop (𝓝 1) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp greenWeight_energy_limit
  have hc : sqrt sineEnergy ≠ 0 := (sqrt_pos.mpr sineEnergy_pos).ne'
  have hh := hs.div_const (sqrt sineEnergy)
  rw [div_self hc] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop 0] with N hn
  have hNr : 0 < (N:ℝ) := by exact_mod_cast hn
  have heps : I.epsilon N ≠ 0 := (one_div_pos.mpr (I.den_pos N)).ne'
  simp only [Function.comp_def]
  rw [gain_exact I N hn, rpow_three_halves, sqrt_div (by positivity), sqrt_cube]
  change sqrt (∑ s ∈ Finset.range N, greenWeight N s^2)/((N:ℝ)*sqrt (N:ℝ))/
    sqrt sineEnergy = _
  field_simp [hc, heps, I.delta_pos.ne', hNr.ne', (sqrt_pos.mpr hNr).ne']

end
end chebyshev1.SineJacobi
