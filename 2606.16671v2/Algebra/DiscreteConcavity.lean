import Mathlib.Tactic

/-!
Article: 2606.16671v2, Theorem E.3.
Nonpositive second differences and a nonnegative initial value force fₙ/n to decrease.
Use: `«2606.16671v2».DiscreteConcavity.normalized_decreasing` feeds
`«2606.16671v2».SineJacobi.endpoint_midpoint_control` (endpoint midpoint control).
Proof chain: `«2606.16671v2».SineJacobi.endpoint_global_bound` — 2606.16671v2, Theorem E.3;
Hard-edge recurrence, singular ODE, uniqueness and endpoint limits.
-/
namespace «2606.16671v2».DiscreteConcavity

/--
Nonpositive second differences and a nonnegative initial value force fₙ/n to decrease.

The stated quantitative bound `f s/(s:ℝ) ≤ f m/(m:ℝ)`.

Use: `«2606.16671v2».SineJacobi.endpoint_midpoint_control` uses this bound to establish the
stated quantitative bound `endpoint N s ≤ 3*endpoint N (N/2)`.

Article: 2606.16671v2, Theorem E.3 via `«2606.16671v2».SineJacobi.endpoint_global_bound`.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem normalized_decreasing (f : ℕ → ℝ) (N : ℕ) (hf0 : 0 ≤ f 0)
    (hconc : ∀ n, n+1 < N → f (n+2)-2*f (n+1)+f n ≤ 0)
    {m s : ℕ} (hm : 0 < m) (hms : m ≤ s) (hs : s ≤ N) :
    f s/(s:ℝ) ≤ f m/(m:ℝ) := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  have hcross : ∀ n, n < N → (n:ℝ)*f (n+1) ≤ ((n:ℝ)+1)*f n := by
    intro n
    induction n with
    | zero => intro _; simpa using hf0
    | succ n ih =>
      intro hn
      have hc := hconc n (by omega)
      have hb := ih (by omega)
      have hmul := mul_nonpos_of_nonneg_of_nonpos
        (show 0 ≤ (n:ℝ)+1 by positivity) hc
      push_cast
      nlinarith
  have hr : ∀ s, m ≤ s → s ≤ N → f s/(s:ℝ) ≤ f m/(m:ℝ) := by
    intro s hms
    induction s, hms using Nat.le_induction with
    | base => intro _; rfl
    | succ s hms ih =>
      intro hs
      have hp : 0 < (s:ℝ) := by exact_mod_cast (show 0 < s by omega)
      have hstep : f (s+1)/((s+1:ℕ):ℝ) ≤ f s/(s:ℝ) := by
        apply (div_le_div_iff₀ (by positivity) hp).mpr
        simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using hcross s (by omega)
      exact hstep.trans (ih (by omega))
  exact hr s hms hs

end «2606.16671v2».DiscreteConcavity
