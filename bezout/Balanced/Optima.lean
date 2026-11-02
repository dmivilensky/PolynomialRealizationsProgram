import bezout.Balanced.Gains
import bezout.Gains.Witness

/-!
Article: bezout, Theorem 4.1 (`thm:linear`).
Use: the constructed six-slot Balanced history attains the sharp spectral,
operator, local-relative and both Hilbert--Schmidt minima for every N>=2.
The unrestricted comparison class includes signed coefficients and arbitrary
memory. No positivity assumption is imposed on competing histories.
Proof: positive factors give all upper bounds; actual symmetric spectral
witnesses and the sign-unrestricted four-corner obstruction give the lower
bounds, with the exact odd-horizon correction.
-/

namespace bezout.Balanced
noncomputable section

/-- Balanced attains the operator-norm optimum for either perturbation class. -/
theorem operatorGain_eq (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (symmetric : Bool) : Gains.operatorGain (history I N hN) I symmetric = Lower.linearGain I N := by
  apply le_antisymm
  · exact csInf_le ⟨0, fun C hb => Gains.operatorBound_nonneg _ I symmetric C hb⟩
      (operatorBound I N hN symmetric)
  · exact Gains.linearGain_le_operatorGain _ I (history_exact I N hN) hN symmetric

/-- Balanced attains the actual-query local relative optimum. -/
theorem localRelativeGain_eq (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) :
    Gains.localRelativeGain (history I N hN) I = Lower.linearGain I N := by
  apply le_antisymm
  · exact csInf_le ⟨0, fun C hb => Gains.localRelativeBound_nonneg _ I C hb⟩
      (localRelativeBound I N hN)
  · exact Gains.linearGain_le_localRelativeGain _ I (history_exact I N hN) hN

/-- Balanced attains the Hilbert--Schmidt optimum for both arbitrary and symmetric perturbations. -/
theorem hsGain_eq_for_class (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (symmetric : Bool) : Gains.hsGain (history I N hN) I symmetric = Lower.linearGain I N := by
  apply le_antisymm
  · exact csInf_le ⟨0, fun _ hb => hb.1⟩ (hsBound I N hN symmetric)
  · exact Gains.linearGain_le_hsGain _ I (history_exact I N hN) hN symmetric

/-- All gains in the linear optimum theorem agree on the same actual history. -/
theorem linear_optima (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) :
    (history I N hN).spectralGain I = Lower.linearGain I N ∧
      Gains.localRelativeGain (history I N hN) I = Lower.linearGain I N ∧
      (∀ symmetric : Bool, Gains.operatorGain (history I N hN) I symmetric = Lower.linearGain I N) ∧
      ∀ symmetric : Bool, Gains.hsGain (history I N hN) I symmetric = Lower.linearGain I N :=
  ⟨spectralGain_eq I N hN, localRelativeGain_eq I N hN,
    operatorGain_eq I N hN, hsGain_eq_for_class I N hN⟩

/-- The physical spectral optimum is an attained minimum over every exact history. -/
theorem spectral_minimum (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) :
    IsLeast {v : ℝ | ∃ h : bezout.History N, h.ChebyshevExact I ∧ v = h.spectralGain I}
      (Lower.linearGain I N) := by
  constructor
  · exact ⟨history I N hN, history_exact I N hN, (spectralGain_eq I N hN).symm⟩
  · rintro v ⟨h, he, rfl⟩
    exact h.linearGain_le_spectralGain I he hN

/-- The operator optimum is attained for arbitrary or symmetric perturbations. -/
theorem operator_minimum (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (symmetric : Bool) :
    IsLeast {v : ℝ | ∃ h : bezout.History N, h.ChebyshevExact I ∧
      v = Gains.operatorGain h I symmetric} (Lower.linearGain I N) := by
  constructor
  · exact ⟨history I N hN, history_exact I N hN, (operatorGain_eq I N hN symmetric).symm⟩
  · rintro v ⟨h, he, rfl⟩
    exact Gains.linearGain_le_operatorGain h I he hN symmetric

/-- The actual-query relative optimum is an attained dimension-uniform minimum. -/
theorem local_relative_minimum (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) :
    IsLeast {v : ℝ | ∃ h : bezout.History N, h.ChebyshevExact I ∧
      v = Gains.localRelativeGain h I} (Lower.linearGain I N) := by
  constructor
  · exact ⟨history I N hN, history_exact I N hN, (localRelativeGain_eq I N hN).symm⟩
  · rintro v ⟨h, he, rfl⟩
    exact Gains.linearGain_le_localRelativeGain h I he hN

/-- The Hilbert--Schmidt optimum is attained under either perturbation class. -/
theorem hs_minimum (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (symmetric : Bool) :
    IsLeast {v : ℝ | ∃ h : bezout.History N, h.ChebyshevExact I ∧
      v = Gains.hsGain h I symmetric} (Lower.linearGain I N) := by
  constructor
  · exact ⟨history I N hN, history_exact I N hN, (hsGain_eq_for_class I N hN symmetric).symm⟩
  · rintro v ⟨h, he, rfl⟩
    exact Gains.linearGain_le_hsGain h I he hN symmetric

end
end bezout.Balanced
