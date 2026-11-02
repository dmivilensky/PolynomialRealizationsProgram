import bezout.Channel.SignalEndpointMethods
import bezout.Comparisons.Competitors.SineComparison

/-!
Article: bezout, the variance separation following Equation
`eq:experiment-endpoint-transfer`.
Use: the literal finite signal matrices of sine--Jacobi and Balanced obey the
endpoint-mass ratio bound, and hence the stated symbolic asymptotic separation.
Proof: their actual endpoint bounds and the proved sine profile-energy limit;
all endpoint masses and spectral data remain arbitrary.
-/

namespace bezout.Channel
noncomputable section
open Filter Topology
open scoped BigOperators
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- The sharp Balanced gain is strictly positive at every article horizon. -/
theorem balanced_spectralGain_pos (I : chebyshev1.SpectralInterval)
    (N : ℕ) (hN : 2≤N) : 0<(bezout.Balanced.history I N hN).spectralGain I := by
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have he : 0<I.epsilon N := one_div_pos.mpr (I.den_pos N)
  have hd := I.delta_pos
  have hc : 0<bezout.Lower.linearCorrectionSq N :=
    lt_of_lt_of_le zero_lt_one (bezout.Properties.linearCorrectionSq_bounds hN).1
  rw [bezout.Balanced.spectralGain_eq]
  unfold bezout.Lower.linearGain bezout.Lower.derivativeScale
  positivity

/-- The actual finite variance ratio retains at least the endpoint signal mass
fraction of the squared ratio of the two actual spectral gains. -/
theorem sine_balanced_variance_ratio_ge (I : chebyshev1.SpectralInterval)
    (N : ℕ) (hN : 2≤N) (lam a : J → ℝ) (F : Finset J)
    (hlam : ∀ j, lam j∈Set.Icc I.mu I.L) (ha : ∑ j, a j^2=1)
    (hF : ∀ j∈F, lam j=I.mu ∨ lam j=I.L) (hmass : 0<endpointMass F a) :
    endpointMass F a*((bezout.Comparisons.Competitors.Sine.history I N).spectralGain I/
        (bezout.Balanced.history I N hN).spectralGain I)^2≤
      rectangularHsSq (signalMatrix (bezout.Comparisons.Competitors.Sine.history I N) lam a)/
        rectangularHsSq (signalMatrix (bezout.Balanced.history I N hN) lam a) := by
  have hsin := sine_signal_endpoint_mass_bounds I N (by omega) lam a F hlam ha hF
  have hbal := balanced_signal_endpoint_mass_bounds I N hN lam a F hlam ha hF
  have hgb := balanced_spectralGain_pos I N hN
  have hs := hsin.1.trans hsin.2.1
  have hbpos : 0<rectangularHsSq (signalMatrix (bezout.Balanced.history I N hN) lam a) :=
    lt_of_lt_of_le (mul_pos hmass (sq_pos_of_pos hgb)) (hbal.1.trans hbal.2.1)
  rw [div_pow,← mul_div_assoc]
  apply (div_le_div_iff₀ (sq_pos_of_pos hgb) hbpos).mpr
  exact (mul_le_mul_of_nonneg_left hbal.2.2
    (mul_nonneg hmass.le (sq_nonneg _))).trans
      (mul_le_mul_of_nonneg_right hs (sq_nonneg _))

/-- The literal ratio of actual finite channel variance coefficients.
The two excluded initial horizons have no effect on its large-horizon limit. -/
def sineBalancedVarianceRatio (I : chebyshev1.SpectralInterval) (lam a : J → ℝ) (N : ℕ) : ℝ :=
  if hN : 2≤N then
    rectangularHsSq (signalMatrix (bezout.Comparisons.Competitors.Sine.history I N) lam a)/
      rectangularHsSq (signalMatrix (bezout.Balanced.history I N hN) lam a)
  else 0

/-- A fully explicit lower sequence for the actual variance ratio. -/
def sineBalancedVarianceLower (I : chebyshev1.SpectralInterval) (ρ : ℝ) (N : ℕ) : ℝ :=
  ρ*((bezout.Comparisons.Competitors.Sine.history I N).spectralGain I/bezout.Lower.linearGain I N)^2

/-- The lower sequence converges to endpoint mass times the symbolic sine constant. -/
theorem sineBalancedVarianceLower_tendsto (I : chebyshev1.SpectralInterval) (ρ : ℝ) :
    Tendsto (sineBalancedVarianceLower I ρ) atTop (𝓝 (ρ*chebyshev1.SineJacobi.sineEnergy)) :=
  (bezout.Comparisons.Competitors.Sine.gain_ratio_sq_limit I).const_mul ρ

/-- The explicit convergent lower sequence bounds the actual signal variances. -/
theorem sineBalancedVarianceLower_eventually_le (I : chebyshev1.SpectralInterval)
    (lam a : J → ℝ) (F : Finset J) (hlam : ∀ j, lam j∈Set.Icc I.mu I.L)
    (ha : ∑ j, a j^2=1) (hF : ∀ j∈F, lam j=I.mu ∨ lam j=I.L)
    (hmass : 0<endpointMass F a) :
    ∀ᶠ N in atTop, sineBalancedVarianceLower I (endpointMass F a) N≤
      sineBalancedVarianceRatio I lam a N := by
  filter_upwards [eventually_ge_atTop 2] with N hN
  simp only [sineBalancedVarianceRatio,hN,dite_true,sineBalancedVarianceLower]
  have hb := sine_balanced_variance_ratio_ge I N hN lam a F hlam ha hF hmass
  simpa only [bezout.Balanced.spectralGain_eq] using hb

/-- Literal asymptotic variance separation: every positive error tolerance
is eventually beaten by endpoint mass times the sine constant minus that tolerance. -/
theorem sine_balanced_variance_separation (I : chebyshev1.SpectralInterval)
    (lam a : J → ℝ) (F : Finset J) (hlam : ∀ j, lam j∈Set.Icc I.mu I.L)
    (ha : ∑ j, a j^2=1) (hF : ∀ j∈F, lam j=I.mu ∨ lam j=I.L)
    (hmass : 0<endpointMass F a) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N in atTop, endpointMass F a*chebyshev1.SineJacobi.sineEnergy-ε≤
      sineBalancedVarianceRatio I lam a N := by
  have hl := (tendsto_order.mp (sineBalancedVarianceLower_tendsto I (endpointMass F a))).1
    (endpointMass F a*chebyshev1.SineJacobi.sineEnergy-ε) (by linarith)
  filter_upwards [hl,sineBalancedVarianceLower_eventually_le I lam a F hlam ha hF hmass]
    with N hlt hle
  exact hlt.le.trans hle

end
end bezout.Channel
