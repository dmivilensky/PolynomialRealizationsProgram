import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
Article: `main_krylov`, `apC:lem:stieltjes` and the state following `apC:eq:rec`.
Finite strings are actual positive masses and gaps, with a nonnegative terminal
Robin parameter. `N` counts edges, so the string has `N+1` mass sites. Natural
indices keep finite-grid limits uncluttered; conclusions state their exact
physical index ranges. All states are constructed by drift followed by the
next genuine mass impulse, rather than supplied with desired recurrences.
Source: the elementary discrete Stieltjes string equation at ζ=−1.
-/

namespace krylov.Strings
noncomputable section
open scoped BigOperators

/-- A genuine finite string with `N+1` masses and `N` positive gaps. Values of
the natural-indexed arrays outside the physical range have no significance. -/
structure DiscreteString (N : ℕ) where
  /-- Actual mass of each site; site zero is distinguished. -/
  mass : ℕ → ℝ
  /-- Actual gap from site `k` to site `k+1`. -/
  gap : ℕ → ℝ
  /-- The source normalizes the initial mass to one. -/
  mass_zero : mass 0 = 1
  /-- Every physical site has strictly positive mass. -/
  mass_pos : ∀ k ≤ N, 0 < mass k
  /-- Every physical adjacent gap is strictly positive. -/
  gap_pos : ∀ k < N, 0 < gap k
  /-- Nonnegative terminal Robin spring. -/
  robin : ℝ
  /-- The terminal boundary contribution is positive semidefinite. -/
  robin_nonneg : 0 ≤ robin

namespace DiscreteString
variable {N : ℕ} (S : DiscreteString N)

/-- The actual post-mass physical state at ζ=−1. -/
def state : ℕ → ℝ × ℝ × ℝ
  | 0 => (1, 1, 1)
  | k + 1 =>
    let z := state k
    let q := z.1 + S.gap k * z.2.1
    (q, z.2.1 + S.mass (k + 1) * q, z.2.2 + S.mass (k + 1) * q ^ 2)

/-- Position at the actual mass site. -/
def φ (k : ℕ) : ℝ := (S.state k).1
/-- Slope immediately after the actual mass at that site. -/
def p (k : ℕ) : ℝ := (S.state k).2.1
/-- Cumulative state energy through the actual mass site. -/
def K (k : ℕ) : ℝ := (S.state k).2.2

@[simp] theorem φ_zero : S.φ 0 = 1 := rfl
@[simp] theorem p_zero : S.p 0 = 1 := rfl
@[simp] theorem K_zero : S.K 0 = 1 := rfl

/-- Exact free drift over the actual intervening gap. -/
theorem φ_succ (k : ℕ) : S.φ (k + 1) = S.φ k + S.gap k * S.p k := rfl
/-- Exact slope impulse from the next actual mass. -/
theorem p_succ (k : ℕ) : S.p (k + 1) = S.p k + S.mass (k + 1) * S.φ (k + 1) := rfl
/-- Exact energy impulse from the next actual mass. -/
theorem K_succ (k : ℕ) : S.K (k + 1) = S.K k + S.mass (k + 1) * S.φ (k + 1) ^ 2 := rfl

/-- Positivity and the Bellman state-domain inequality are derived from the
actual finite physical masses and gaps. -/
theorem state_bounds (k : ℕ) (hk : k ≤ N) :
    1 ≤ S.φ k ∧ 1 ≤ S.p k ∧ 1 ≤ S.K k ∧ S.K k ≤ S.φ k * S.p k := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨hφ, hp, hK, hr⟩ := ih (by omega)
    have hl := (S.gap_pos k (by omega)).le
    have hm := (S.mass_pos (k + 1) hk).le
    have hφ' : 1 ≤ S.φ (k + 1) := by
      rw [φ_succ]
      nlinarith [mul_nonneg hl (show 0 ≤ S.p k by linarith)]
    have hp' : 1 ≤ S.p (k + 1) := by
      rw [p_succ]
      nlinarith [mul_nonneg hm (show 0 ≤ S.φ (k + 1) by linarith)]
    have hK' : 1 ≤ S.K (k + 1) := by
      rw [K_succ]
      nlinarith [mul_nonneg hm (sq_nonneg (S.φ (k + 1)))]
    refine ⟨hφ', hp', hK', ?_⟩
    have he : S.φ (k + 1) * S.p (k + 1) - S.K (k + 1) =
        S.φ k * S.p k - S.K k + S.gap k * S.p k ^ 2 := by
      rw [p_succ, K_succ, φ_succ]
      ring
    nlinarith [mul_nonneg hl (sq_nonneg (S.p k))]

/-- The actual state ratio used in the continuum comparison. -/
def ratio (k : ℕ) : ℝ := S.φ k * S.p k / S.K k

theorem ratio_ge_one (k : ℕ) (hk : k ≤ N) : 1 ≤ S.ratio k := by
  obtain ⟨_, _, hK, hr⟩ := S.state_bounds k hk
  exact (le_div_iff₀ (show 0 < S.K k by linarith)).2 (by simpa using hr)

/-- The cumulative physical state energy is precisely the discrete
Christoffel denominator once the spectral polynomials are identified. -/
theorem K_eq_sum (k : ℕ) : S.K k =
    ∑ i ∈ Finset.range (k + 1), S.mass i * S.φ i ^ 2 := by
  induction k with
  | zero => simp [S.mass_zero]
  | succ k ih => rw [K_succ, Finset.sum_range_succ, ← ih]

end DiscreteString
end
end krylov.Strings
