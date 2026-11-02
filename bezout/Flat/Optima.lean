import bezout.Flat.Response
import bezout.Risk.Attainment

/-!
Article: bezout, Theorem 3.1 (`thm:additive`).
Use: the explicitly constructed Flat history attains both exact unrestricted
additive minima for every horizon, interval and nonnegative error budget.
Proof: its equal physical responses give the universal upper bounds, while
the actual scalar deterministic and martingale witnesses force both values.
-/

namespace bezout.Flat
noncomputable section
open scoped BigOperators

/-- The actual Flat history attains the exact universal deterministic risk. -/
theorem additiveRisk_eq (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (r t : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t) :
    Risk.additiveRisk (history I N hN) I r t = Risk.additiveOptimum I N r t :=
  Risk.additiveRisk_eq_of_equal_responses _ I (history_exact I N hN) (by omega)
    (fun s _ hx => response_abs_le I N hN s hx) r t hr ht

/-- The same actual Flat history attains the exact worst-case martingale MSE. -/
theorem mseRisk_eq (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (r σ : ℝ) (hr : 0 ≤ r) :
    Risk.mseRisk (history I N hN) I r σ = Risk.mseOptimum I N r σ :=
  Risk.mseRisk_eq_of_equal_responses _ I (history_exact I N hN) (by omega)
    (fun s _ hx => response_abs_le I N hN s hx) r σ hr

/-- The exact deterministic minimax is an attained minimum over the entire
Chebyshev-exact history class, with no sign or memory restrictions. -/
theorem additive_minimum (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (r t : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t) :
    IsLeast {v : ℝ | ∃ h : bezout.History N, h.ChebyshevExact I ∧
      v = Risk.additiveRisk h I r t} (Risk.additiveOptimum I N r t) := by
  constructor
  · exact ⟨history I N hN, history_exact I N hN, (additiveRisk_eq I N hN r t hr ht).symm⟩
  · rintro v ⟨h, he, rfl⟩
    exact Risk.additiveRisk_lower h I he (by omega) r t hr ht

/-- The exact martingale minimax is attained by that same Flat history. -/
theorem mse_minimum (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (r σ : ℝ) (hr : 0 ≤ r) :
    IsLeast {v : ℝ | ∃ h : bezout.History N, h.ChebyshevExact I ∧
      v = Risk.mseRisk h I r σ} (Risk.mseOptimum I N r σ) := by
  constructor
  · exact ⟨history I N hN, history_exact I N hN, (mseRisk_eq I N hN r σ hr).symm⟩
  · rintro v ⟨h, he, rfl⟩
    exact Risk.mseRisk_lower h I he (by omega) r σ hr

end
end bezout.Flat
