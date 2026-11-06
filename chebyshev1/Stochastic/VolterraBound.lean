import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Tactic

/-! Finite scalar majorants for state-dependent second moments. -/
namespace chebyshev1.Stochastic
open scoped BigOperators

/-- Discrete Gronwall in a form that includes `A = 0` and uses no division. -/
theorem discrete_volterra_bound {X : ℕ → ℝ} {M A : ℝ} {N : ℕ}
    (hA : 0 ≤ A) (hrec : ∀ t ≤ N, X t ≤ M+A*∑ s ∈ Finset.range t, X s) :
    ∀ t ≤ N, X t ≤ M*(1+A)^t := by
  have hsum (t : ℕ) (ht : t ≤ N+1) :
      A*∑ s ∈ Finset.range t, X s ≤ M*((1+A)^t-1) := by
    induction t with
    | zero => simp
    | succ t ih =>
      have hp := ih (by omega)
      have hx := hrec t (by omega)
      have hmul := mul_le_mul_of_nonneg_left hx hA
      have hg := mul_le_mul_of_nonneg_left hp (show 0 ≤ 1+A by linarith)
      rw [Finset.sum_range_succ, mul_add, pow_succ]
      nlinarith
  intro t ht
  exact (hrec t ht).trans (by linarith [hsum t (by omega)])

/-- A finite-horizon bound uniform in the small nonnegative noise parameter. -/
theorem discrete_volterra_uniform {X : ℕ → ℝ} {M A q : ℝ} {N : ℕ}
    (hA : 0 ≤ A) (hq1 : q ≤ 1)
    (hX : ∀ t ≤ N, 0 ≤ X t)
    (hrec : ∀ t ≤ N, X t ≤ M+q*A*∑ s ∈ Finset.range t, X s) :
    ∀ t ≤ N, X t ≤ M*(1+A)^t := by
  apply discrete_volterra_bound hA
  intro t ht
  have hs : 0 ≤ ∑ s ∈ Finset.range t, X s :=
    Finset.sum_nonneg (fun s hs => hX s (by have := Finset.mem_range.mp hs; omega))
  have hqa : q*A ≤ A := by nlinarith
  exact (hrec t ht).trans (by nlinarith)

theorem discrete_volterra_sum_bound {X : ℕ → ℝ} {M A q : ℝ} {N : ℕ}
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hq1 : q ≤ 1)
    (hX : ∀ t ≤ N, 0 ≤ X t)
    (hrec : ∀ t ≤ N, X t ≤ M+q*A*∑ s ∈ Finset.range t, X s) :
    (∑ s ∈ Finset.range N, X s) ≤ (N:ℝ)*M*(1+A)^N := by
  have hb := discrete_volterra_uniform hA hq1 hX hrec
  calc
    _ ≤ ∑ _s ∈ Finset.range N, M*(1+A)^N := by
      apply Finset.sum_le_sum
      intro s hs
      have hsN := (Finset.mem_range.mp hs).le
      exact (hb s hsN).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ 1+A) hsN) hM)
    _ = _ := by simp [mul_assoc]

theorem discrete_volterra_forcing_bound {X : ℕ → ℝ} {M A q : ℝ} {N : ℕ}
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hX : ∀ t ≤ N, 0 ≤ X t)
    (hrec : ∀ t ≤ N, X t ≤ M+q*A*∑ s ∈ Finset.range t, X s) :
    q*A*(∑ s ∈ Finset.range N, X s) ≤ q*A*(N:ℝ)*M*(1+A)^N := by
  have h := mul_le_mul_of_nonneg_left
    (discrete_volterra_sum_bound hM hA hq1 hX hrec) (mul_nonneg hq hA)
  simpa only [mul_assoc] using h

end chebyshev1.Stochastic
