import krylov.Stability.WeightedCompactTaylor
import Mathlib.Analysis.Analytic.ChangeOrigin

/-!
Article: main_krylov, lem:U(a,d), compact Taylor bounds on actual analytic reference sets.
Use: turn pointwise analytic algorithmic regularity at every reference into
one genuine smooth neighborhood and uniform compact Taylor constants.
Source: mathlib's open analytic locus and the proved compact integral Taylor calculus.
-/

namespace krylov.Stability
noncomputable section
variable {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Actual analyticity at every point of a compact reference set gives one common neighborhood and all finite Taylor orders.
Use: all actual analytically executed policy outputs share the same compact-calculus bridge.
Article: main_krylov, lem:U(a,d).
Proof: the true analytic locus is open and contains the entire actual
reference compact; it is a genuine C^r domain for every finite r, so the proved
compact Taylor theorem applies without any assumed trajectory remainder. -/
theorem compact_analytic_taylor (f : X → F) (K : Set X) (hK : IsCompact K)
    (hf : ∀ x∈K, AnalyticAt ℝ f x) (r : ℕ) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ h : X, ‖h‖≤δ → ∀ k : ℕ, 1≤k → k≤r →
      ‖f (x+h)-taylorPolynomial f k x h‖≤C*‖h‖^k := by
  apply compact_taylor_remainders f r {x | AnalyticAt ℝ f x} K (isOpen_analyticAt ℝ f) hK hf
  intro x hx
  exact hx.contDiffAt.contDiffWithinAt

/-- Actual compact analytic reference sets admit the printed positive continuous initial-error weight uniformly at every finite order.
Use: the compact algorithmic remainder includes its genuine reference normalization factor.
Article: main_krylov, lem:U(a,d), weighted compact remainder.
Proof: apply the proved weighted compact Taylor theorem to the actual open
analytic locus, where genuine analyticity supplies every required smooth derivative. -/
theorem compact_analytic_weighted_taylor (f : X → F) (e : X → ℝ) (K : Set X) (hK : IsCompact K)
    (hf : ∀ x∈K, AnalyticAt ℝ f x) (he : ContinuousOn e K) (hepos : ∀ x∈K, 0<e x) (r : ℕ) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ h : X, ‖h‖≤δ → ∀ k : ℕ, 1≤k → k≤r →
      ‖f (x+h)-taylorPolynomial f k x h‖≤C*‖h‖^k*e x := by
  exact compact_weighted_taylor f e r {x | AnalyticAt ℝ f x} K (isOpen_analyticAt ℝ f) hK hf
    (fun _ hx => hx.contDiffAt.contDiffWithinAt) he hepos

end
end krylov.Stability
