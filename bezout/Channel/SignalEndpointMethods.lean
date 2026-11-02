import bezout.Channel.SignalWeights

/-!
Article: bezout, Equation `eq:experiment-endpoint-transfer`.
Use: the general endpoint-mass bounds apply to the actual Prefix,
sine--Jacobi and Balanced histories at every admissible horizon.
Proof: the proven signed endpoint profiles and endpoint maximum principles.
-/

namespace bezout.Channel
noncomputable section
open scoped BigOperators
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Exact endpoint-mass transfer for the literal prefix iteration. -/
theorem prefix_signal_endpoint_mass_bounds (I : chebyshev1.SpectralInterval)
    (N : ℕ) (hN : 0<N) (lam a : J → ℝ) (F : Finset J)
    (hlam : ∀ j, lam j∈Set.Icc I.mu I.L) (ha : ∑ j, a j^2=1)
    (hF : ∀ j∈F, lam j=I.mu ∨ lam j=I.L) :
    endpointMass F a*(bezout.Comparisons.Competitors.Prefix.history I N).spectralGain I^2≤
        rectangularNorm (signalMatrix (bezout.Comparisons.Competitors.Prefix.history I N) lam a)^2 ∧
      rectangularNorm (signalMatrix (bezout.Comparisons.Competitors.Prefix.history I N) lam a)^2≤
        rectangularHsSq (signalMatrix (bezout.Comparisons.Competitors.Prefix.history I N) lam a) ∧
      rectangularHsSq (signalMatrix (bezout.Comparisons.Competitors.Prefix.history I N) lam a)≤
        (bezout.Comparisons.Competitors.Prefix.history I N).spectralGain I^2 := by
  apply signal_endpoint_mass_bounds _ I lam a F ((-1:ℝ)^(N-1))
    (by rw [← pow_mul]; simp [mul_comm (N-1) 2,pow_mul]) hlam ha hF
  · exact bezout.Comparisons.Competitors.Prefix.endpoint_profile I N hN
  · exact bezout.Comparisons.Competitors.Prefix.gain_endpoint I N hN

/-- Exact endpoint-mass transfer for the literal sine iteration. -/
theorem sine_signal_endpoint_mass_bounds (I : chebyshev1.SpectralInterval)
    (N : ℕ) (hN : 0<N) (lam a : J → ℝ) (F : Finset J)
    (hlam : ∀ j, lam j∈Set.Icc I.mu I.L) (ha : ∑ j, a j^2=1)
    (hF : ∀ j∈F, lam j=I.mu ∨ lam j=I.L) :
    endpointMass F a*(bezout.Comparisons.Competitors.Sine.history I N).spectralGain I^2≤
        rectangularNorm (signalMatrix (bezout.Comparisons.Competitors.Sine.history I N) lam a)^2 ∧
      rectangularNorm (signalMatrix (bezout.Comparisons.Competitors.Sine.history I N) lam a)^2≤
        rectangularHsSq (signalMatrix (bezout.Comparisons.Competitors.Sine.history I N) lam a) ∧
      rectangularHsSq (signalMatrix (bezout.Comparisons.Competitors.Sine.history I N) lam a)≤
        (bezout.Comparisons.Competitors.Sine.history I N).spectralGain I^2 := by
  apply signal_endpoint_mass_bounds _ I lam a F ((-1:ℝ)^(N-1))
    (by rw [← pow_mul]; simp [mul_comm (N-1) 2,pow_mul]) hlam ha hF
  · exact bezout.Comparisons.Competitors.Sine.endpoint_profile I N hN
  · exact bezout.Comparisons.Competitors.Sine.gain_endpoint I N hN

/-- Exact endpoint-mass transfer for the literal balanced iteration. -/
theorem balanced_signal_endpoint_mass_bounds (I : chebyshev1.SpectralInterval)
    (N : ℕ) (hN : 2≤N) (lam a : J → ℝ) (F : Finset J)
    (hlam : ∀ j, lam j∈Set.Icc I.mu I.L) (ha : ∑ j, a j^2=1)
    (hF : ∀ j∈F, lam j=I.mu ∨ lam j=I.L) :
    endpointMass F a*(bezout.Balanced.history I N hN).spectralGain I^2≤
        rectangularNorm (signalMatrix (bezout.Balanced.history I N hN) lam a)^2 ∧
      rectangularNorm (signalMatrix (bezout.Balanced.history I N hN) lam a)^2≤
        rectangularHsSq (signalMatrix (bezout.Balanced.history I N hN) lam a) ∧
      rectangularHsSq (signalMatrix (bezout.Balanced.history I N hN) lam a)≤
        (bezout.Balanced.history I N hN).spectralGain I^2 := by
  apply signal_endpoint_mass_bounds _ I lam a F ((-1:ℝ)^(N-1))
    (by rw [← pow_mul]; simp [mul_comm (N-1) 2,pow_mul]) hlam ha hF
  · exact bezout.Comparisons.Competitors.BalancedEndpoints.endpoint_profile I N hN
  · exact bezout.Comparisons.Competitors.BalancedEndpoints.gain_endpoint I N hN

end
end bezout.Channel
