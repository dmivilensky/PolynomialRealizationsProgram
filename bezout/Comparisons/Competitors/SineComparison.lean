import bezout.Comparisons.Competitors.Endpoints
import bezout.Properties.Asymptotics
import chebyshev1.SineJacobi.Comparison

/-!
Article: bezout, the symbolic sine--Jacobi/Balanced comparison after Equation
`eq:experiment-endpoint-transfer`.
Use: the comparison concerns the gains of the actual oracle programs. Its
limiting constant is the proved sine profile integral, without decimal data.
Proof: cancel the common Chebyshev terminal scale in the exact finite energies;
the parity correction tends to one and the sine profile energy converges.
-/

namespace bezout.Comparisons.Competitors.Sine
noncomputable section
open chebyshev1 Filter Topology
open scoped BigOperators

/-- The exact squared gain of the literal sine--Jacobi physical history. -/
theorem gain_sq (I : SpectralInterval) (N : ℕ) (hN : 0<N) :
    (history I N).spectralGain I ^ 2=(2*I.epsilon N/I.delta)^2*
      ∑ s ∈ Finset.range N, SineJacobi.greenWeight N s^2 := by
  rw [gain_eq I N hN,SineJacobi.gain_exact I N hN,mul_pow,
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

/-- The finite squared ratio retains the exact odd-horizon correction. -/
theorem gain_ratio_sq (I : SpectralInterval) (N : ℕ) (hN : 2≤N) :
    ((history I N).spectralGain I/bezout.Lower.linearGain I N)^2=
      ((∑ s ∈ Finset.range N, SineJacobi.greenWeight N s^2)/(N:ℝ)^3)/
        bezout.Lower.linearCorrectionSq N := by
  have hn : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega)
  have he : I.epsilon N≠0 := (one_div_pos.mpr (I.den_pos N)).ne'
  have hc : bezout.Lower.linearCorrectionSq N≠0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num) (bezout.Properties.linearCorrectionSq_bounds hN).1)
  rw [div_pow,gain_sq I N (by omega),bezout.Lower.linearGain_sq I hN]
  unfold bezout.Lower.derivativeScale
  field_simp [hn,he,I.delta_pos.ne',hc]

/-- This is the finite ratio of the two actual histories, without a surrogate gain. -/
theorem gain_ratio_balanced_sq (I : SpectralInterval) (N : ℕ) (hN : 2≤N) :
    ((history I N).spectralGain I/(bezout.Balanced.history I N hN).spectralGain I)^2=
      ((∑ s ∈ Finset.range N, SineJacobi.greenWeight N s^2)/(N:ℝ)^3)/
        bezout.Lower.linearCorrectionSq N := by
  rw [bezout.Balanced.spectralGain_eq]
  exact gain_ratio_sq I N hN

/-- The squared correction itself tends to one, in both parities. -/
theorem correction_sq_tendsto_one :
    Tendsto bezout.Lower.linearCorrectionSq atTop (𝓝 (1:ℝ)) := by
  have hc := bezout.Properties.linearCorrection_tendsto_one.pow 2
  norm_num only [one_pow] at hc
  apply hc.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact Real.sq_sqrt (bezout.Lower.linearCorrectionSq_nonneg hN)

/-- The exact physical gain ratio converges to the symbolic sine profile energy. -/
theorem gain_ratio_sq_limit (I : SpectralInterval) :
    Tendsto (fun N : ℕ => ((history I N).spectralGain I/bezout.Lower.linearGain I N)^2)
      atTop (𝓝 SineJacobi.sineEnergy) := by
  have hl := SineJacobi.greenWeight_energy_limit.div correction_sq_tendsto_one (by norm_num)
  simp only [div_one] at hl
  apply hl.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact (gain_ratio_sq I N hN).symm

/-- The actual sine competitor is eventually strictly better than actual Prefix. -/
theorem gain_eventually_lt_prefix (I : SpectralInterval) :
    ∀ᶠ N : ℕ in atTop, (history I N).spectralGain I<(Prefix.history I N).spectralGain I := by
  filter_upwards [SineJacobi.gain_eventually_lt_prefix I,eventually_gt_atTop 0] with N h hN
  rw [gain_eq I N hN,Prefix.history_eq_classical,bezout.Classical.spectralGain_eq_prefix I N hN]
  exact h

end
end bezout.Comparisons.Competitors.Sine
