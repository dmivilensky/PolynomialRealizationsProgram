import nesterov.Momentum.Execution
import nesterov.Quadratic.ScalarRecurrence

/-!
Article: Appendix C, Lemma `restquad`.
Use: exact literal nth-root limsups of the actual from-rest scalar iterates
and queries, with no nonnegative-determinant restriction.  The only excluded
query case is precisely β=τ/(1+τ), as in the article.
-/

noncomputable section

namespace nesterov.Momentum

open Filter Quadratic
open scoped Topology

theorem quadratic_iterate_recurrence (β τ h lam x₀ : ℝ) :
    ScalarRecurrence (S β τ h lam) (Q β τ h lam)
      (iterate (fun x : ℝ => lam * x) β τ h x₀) := by
  intro n
  rw [iterate_recurrence, queryIterate_succ]
  simp only [smul_eq_mul]
  dsimp [S, Q]
  ring

theorem quadratic_query_recurrence (β τ h lam x₀ : ℝ) :
    ScalarRecurrence (S β τ h lam) (Q β τ h lam)
      (queryIterate (fun x : ℝ => lam * x) β τ h x₀) := by
  intro n
  rw [queryIterate_recurrence]
  simp only [smul_eq_mul]
  dsimp [S, Q]
  ring

/-- Lemma restquad: the actual scalar iterates have every dominant mode
excited by the fixed initialization x_{-1}=x_0≠0. -/
theorem quadratic_iterate_root_limsup {β τ h lam x₀ : ℝ}
    (hh : 0 < h) (hlam : 0 < lam) (hx₀ : x₀ ≠ 0) :
    limsup (fun n : ℕ => |iterate (fun x : ℝ => lam * x) β τ h x₀ n| ^ ((n : ℝ)⁻¹)) atTop =
      scalarRadius β τ h lam := by
  refine (quadratic_iterate_recurrence β τ h lam x₀).root_limsup_eq
    (b := Q β τ h lam) (x₀ := x₀) (by simp) ?_ hx₀ ?_
  · rw [iterate_one]
    simp only [smul_eq_mul]
    dsimp [S, Q]
    ring
  · intro r hr hr0 heq
    have hq : Q β τ h lam ≠ 0 := by
      intro hq
      apply hr0
      rw [heq, hq, Complex.ofReal_zero]
    rw [heq] at hr
    have hr' : (Q β τ h lam) ^ 2 - S β τ h lam * Q β τ h lam + Q β τ h lam = 0 := by
      exact_mod_cast hr
    have hchar1 : 1 + Q β τ h lam - S β τ h lam = h * lam := by dsimp [S, Q]; ring
    have hp : Q β τ h lam * (h * lam) = 0 := by
      rw [← hchar1]
      nlinarith
    exact (mul_ne_zero hq (ne_of_gt (mul_pos hh hlam))) hp

/-- Lemma restquad: the actual gradient queries excite every dominant mode
unless the tuning has the article's exact common-factor degeneracy. -/
theorem quadratic_query_root_limsup {β τ h lam x₀ : ℝ}
    (hh : 0 < h) (hlam : 0 < lam) (hx₀ : x₀ ≠ 0) (hτ : 0 ≤ τ)
    (hne : β ≠ τ / (1 + τ)) :
    limsup (fun n : ℕ => |queryIterate (fun x : ℝ => lam * x) β τ h x₀ n| ^ ((n : ℝ)⁻¹)) atTop =
      scalarRadius β τ h lam := by
  refine (quadratic_query_recurrence β τ h lam x₀).root_limsup_eq
    (b := β) (x₀ := x₀) (by simp) ?_ hx₀ ?_
  · rw [queryIterate_one]
    simp only [smul_eq_mul]
    dsimp [S]
    ring
  · intro r hr _ heq
    rw [heq] at hr
    have hr' : β ^ 2 - S β τ h lam * β + Q β τ h lam = 0 := by exact_mod_cast hr
    have hN : (1 + τ) * β - τ ≠ 0 := by
      intro hz
      apply hne
      apply (eq_div_iff (show 1 + τ ≠ 0 by linarith)).mpr
      nlinarith
    have hp : (h * lam) * ((1 + τ) * β - τ) = 0 := by
      dsimp [S, Q] at hr'
      linear_combination hr'
    exact (mul_ne_zero (ne_of_gt (mul_pos hh hlam)) hN) hp

end nesterov.Momentum
