import bezout.Algorithms.BalancedScalarCost

/-!
Article: bezout, Algorithm 2, well-defined scalar preparation at all horizons.
Use: every real division evaluated by the cached arithmetic program has a
nonzero denominator, including startup and final reverse-parity boundaries.
Proof: cached Chebyshev and omega values have proved positive denominators;
the actual prefix theorem transfers these certificates to the executed cache.
-/

namespace bezout.Algorithms.Balanced
noncomputable section
open Polynomial Polynomial.Chebyshev

/-- The cached real omega cell has its proved positive scalar value. -/
theorem safety_cache_omega (I : chebyshev1.SpectralInterval) {N j : ℕ} (hj : j<N) :
    scalarValue I N (forwardIndex j 1) = bezout.Balanced.omega N j := by
  rw [scalarValue_forward I hj.le (by omega)]
  simp only [forwardValue, hj, ite_true, Nat.reduceEqDiff, ite_false]

/-- The cached real C cell has its exact prepared Chebyshev value. -/
theorem safety_cache_C (I : chebyshev1.SpectralInterval) {N j : ℕ} (hj : j≤N) :
    scalarValue I N (forwardIndex j 0) = preparedC I j := by
  rw [scalarValue_forward I hj (by omega)]
  rfl

/-- Every closed parity-weight arithmetic expression has a nonzero divisor. -/
theorem omegaExpr_defined (I : chebyshev1.SpectralInterval) {N : ℕ} (hN : 2≤N) (j : ℕ) :
    (omegaExpr N j).Defined (scalarInputs I) (scalarValue I N) := by
  have hn : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega)
  have hn1 : (N:ℝ)+1≠0 := ne_of_gt (by positivity)
  have hn2 : (N:ℝ)*(N:ℝ)+1≠0 := ne_of_gt (by positivity)
  unfold omegaExpr
  split_ifs <;> simp [ScalarExpr.Defined, hn, hn1, hn2]

/-- A cached-band read performs no division. -/
theorem pastImpulseExpr_defined (inputs memory : ℕ → ℝ) (j d r : ℕ) :
    (pastImpulseExpr j d r).Defined inputs memory := by
  unfold pastImpulseExpr
  split_ifs <;> trivial

/-- Every actually used startup row has only positive Delta/omega denominators. -/
theorem startupImpulseExpr_defined (I : chebyshev1.SpectralInterval) {N j d : ℕ}
    (hN : 2≤N) (hj : j<N) (hj4 : j<4) (hd1 : 1≤d) (hdj : d≤j) :
    (startupImpulseExpr j d).Defined (scalarInputs I) (scalarValue I N) := by
  have hdelta := ne_of_gt I.delta_pos
  interval_cases j
  · omega
  · simp [startupImpulseExpr, ScalarExpr.Defined, scalarInputs, hdelta]
  · simp [startupImpulseExpr, ScalarExpr.Defined, scalarInputs, hdelta, forwardRead]
  · have hw := ne_of_gt (bezout.Balanced.omega_pos hN (show 2<N by omega))
    unfold startupImpulseExpr
    split_ifs <;>
      simp [ScalarExpr.Defined, scalarInputs, hdelta, forwardRead,
        safety_cache_omega I (show 2<N by omega), mul_ne_zero hdelta hw]

/-- The complete four-entry impulse band evaluates only valid startup divisions. -/
theorem impulseExpr_defined (I : chebyshev1.SpectralInterval) {N j d : ℕ}
    (hN : 2≤N) (hd1 : 1≤d) :
    (impulseExpr N j d).Defined (scalarInputs I) (scalarValue I N) := by
  by_cases hg : j<N ∧ d≤j
  · rw [impulseExpr, ite_eq_left hg]
    by_cases hs : j<4
    · rw [ite_eq_left hs]
      exact startupImpulseExpr_defined I hN hg.1 hs hd1 hg.2
    · rw [ite_eq_right hs]
      simp [ScalarExpr.Defined, pastImpulseExpr_defined, forwardRead]
  · simp only [impulseExpr, ite_eq_right hg, ScalarExpr.Defined]

/-- All ten forward cache fields have well-defined evaluated arithmetic. -/
theorem forwardExpr_defined (I : chebyshev1.SpectralInterval) {N j f : ℕ}
    (hN : 2≤N) (_hj : j≤N) (hf : f<10) :
    (forwardExpr N j f).Defined (scalarInputs I) (scalarValue I N) := by
  have hdelta := ne_of_gt I.delta_pos
  interval_cases f
  · simp only [forwardExpr, ite_true]
    split_ifs <;> trivial
  · by_cases hjN : j<N
    · simpa [forwardExpr, hjN] using omegaExpr_defined I hN j
    · simp [forwardExpr, hjN, ScalarExpr.Defined]
  · by_cases hjN : j<N
    · simp only [forwardExpr, hjN, Nat.reduceEqDiff, ite_false, ite_true]
      split_ifs <;> trivial
    · simp [forwardExpr, hjN, ScalarExpr.Defined]
  · by_cases hjN : j<N
    · by_cases hj4 : 4≤j
      · have hw := ne_of_gt (bezout.Balanced.omega_pos hN (show j-1<N by omega))
        simp [forwardExpr, hjN, hj4, ScalarExpr.Defined,
          safety_cache_omega I (show j-1<N by omega), hw, forwardRead]
      · simp [forwardExpr, hjN, hj4, ScalarExpr.Defined]
    · simp [forwardExpr, hjN, ScalarExpr.Defined]
  · by_cases hjN : j<N
    · by_cases hj4 : 4≤j
      · have hw := ne_of_gt (bezout.Balanced.omega_pos hN (show j-2<N by omega))
        simp [forwardExpr, hjN, hj4, ScalarExpr.Defined,
          safety_cache_omega I (show j-2<N by omega), hw, forwardRead]
      · simp [forwardExpr, hjN, hj4, ScalarExpr.Defined]
    · simp [forwardExpr, hjN, ScalarExpr.Defined]
  · by_cases hjN : j<N
    · by_cases hj4 : 4≤j
      · have hw := ne_of_gt (bezout.Balanced.omega_pos hN (show j-1<N by omega))
        simp [forwardExpr, hjN, hj4, ScalarExpr.Defined, scalarInputs,
          safety_cache_omega I (show j-1<N by omega), hw, hdelta, forwardRead]
      · simp [forwardExpr, hjN, hj4, ScalarExpr.Defined]
    · simp [forwardExpr, hjN, ScalarExpr.Defined]
  · by_cases hjN : j<N
    · simpa [forwardExpr, hjN] using impulseExpr_defined I (N:=N) (j:=j) (d:=1) hN (by omega)
    · simp [forwardExpr, hjN, ScalarExpr.Defined]
  · by_cases hjN : j<N
    · simpa [forwardExpr, hjN] using impulseExpr_defined I (N:=N) (j:=j) (d:=2) hN (by omega)
    · simp [forwardExpr, hjN, ScalarExpr.Defined]
  · by_cases hjN : j<N
    · simpa [forwardExpr, hjN] using impulseExpr_defined I (N:=N) (j:=j) (d:=3) hN (by omega)
    · simp [forwardExpr, hjN, ScalarExpr.Defined]
  · by_cases hjN : j<N
    · simpa [forwardExpr, hjN] using impulseExpr_defined I (N:=N) (j:=j) (d:=4) hN (by omega)
    · simp [forwardExpr, hjN, ScalarExpr.Defined]

/-- Reverse accumulation and readout divide only by 2, C_N, Delta and valid omega.
The absent final parity quotient is a literal constant, never a zero division. -/
theorem reverseExpr_defined (I : chebyshev1.SpectralInterval) {N r f : ℕ}
    (hN : 2≤N) (hr : r<N) (_hf : f<3) :
    (reverseExpr N r f).Defined (scalarInputs I) (scalarValue I N) := by
  have hdelta := ne_of_gt I.delta_pos
  have hc : preparedC I N≠0 := by
    rw [preparedC_eq]
    exact I.den_ne N
  have hj : N-1-r<N := by omega
  have hw := ne_of_gt (bezout.Balanced.omega_pos hN hj)
  unfold reverseExpr nextReverseRead
  split_ifs
  all_goals simp [ScalarExpr.Defined, forwardRead, scalarInputs,
    safety_cache_C I le_rfl, safety_cache_omega I hj, hdelta, hc, hw]
  all_goals
    have hw' := ne_of_gt (bezout.Balanced.omega_pos hN (show N-1-r+2<N by omega))
    simpa only [safety_cache_omega I (show N-1-r+2<N by omega)] using hw'

/-- Every arithmetic node of the complete cached Balanced preparation is defined. -/
theorem scalarNode_defined (I : chebyshev1.SpectralInterval) {N k : ℕ}
    (hN : 2≤N) (hk : k<scalarCells N) :
    (scalarNode N k).Defined (scalarInputs I) (scalarValue I N) := by
  unfold scalarNode
  split_ifs with hi
  · apply forwardExpr_defined I hN
    · unfold reverseBase at hi
      omega
    · exact Nat.mod_lt _ (by omega)
  · apply reverseExpr_defined I hN
    · unfold scalarCells at hk
      omega
    · exact Nat.mod_lt _ (by omega)

/-- Each actual cached node is evaluated with all of its division denominators
nonzero. Use: the safety certificate concerns the executed prefix memory. -/
theorem scalarProgram_defined (I : chebyshev1.SpectralInterval) {N : ℕ}
    (hN : 2≤N) (s : Fin (scalarCells N)) :
    ((scalarProgram N).node s).Defined (scalarInputs I)
      (ScalarProgram.extend ((scalarProgram N).runPrefix (scalarInputs I) s.val).values) := by
  apply (scalarProgram N).runPrefix_defined_nat _ _
  · intro j
    exact scalarNode_eval I hN j.isLt
  · intro j
    exact scalarNode_defined I hN j.isLt

end
end bezout.Algorithms.Balanced
