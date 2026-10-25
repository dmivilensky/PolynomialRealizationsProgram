import polyak.Dynamics.Quadratic
import polyak.Dynamics.Iteration
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
Article: introduction eq:quad and Appendix A, decay of the scalar quadratic recurrence.
Use: true convergence of every scalar solution, including repeated and zero roots.
Proof: factor the recurrence, bound its forced first-order solution by n times
a geometric sequence, and apply the corresponding real limit theorem.
-/

namespace polyak.Dynamics
noncomputable section
open Filter
open scoped Topology

/-- Article: scalar quadratic stability. Use: no distinct-root assumption is needed. -/
theorem recurrence_tendsto_zero_of_roots (u : ℕ → ℂ) (r s : ℂ)
    (hr : ‖r‖ < 1) (hs : ‖s‖ < 1)
    (hrec : ∀ n, u (n+2) = (r+s)*u (n+1) - (r*s)*u n) :
    Tendsto u atTop (𝓝 0) := by
  let γ := max ‖r‖ ‖s‖
  let D := ‖u 1-s*u 0‖
  have hγ0 : 0 ≤ γ := (norm_nonneg r).trans (le_max_left _ _)
  have hγ1 : γ < 1 := max_lt hr hs
  have hrr : ‖r‖ ≤ γ := le_max_left _ _
  have hss : ‖s‖ ≤ γ := le_max_right _ _
  have hD : 0 ≤ D := norm_nonneg _
  have hdiff (n : ℕ) : u (n+1)-s*u n = r^n*(u 1-s*u 0) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show n+1+1=n+2 by omega, hrec]
      calc
        _ = r*(u (n+1)-s*u n) := by ring
        _ = _ := by rw [ih, pow_succ]; ring
  have hone (n : ℕ) : ‖u (n+1)‖ ≤ γ*‖u n‖ + D*γ^n := by
    have he : u (n+1) = s*u n + r^n*(u 1-s*u 0) := by
      have := hdiff n
      linear_combination this
    rw [he]
    calc
      _ ≤ ‖s*u n‖ + ‖r^n*(u 1-s*u 0)‖ := norm_add_le _ _
      _ = ‖s‖*‖u n‖ + ‖r‖^n*D := by rw [norm_mul, norm_mul, norm_pow]
      _ ≤ γ*‖u n‖ + γ^n*D := by gcongr
      _ = _ := by ring
  have hbound (n : ℕ) : ‖u (n+1)‖ ≤ ‖u 0‖*γ^(n+1) + ((n : ℝ)+1)*D*γ^n := by
    induction n with
    | zero => simpa [mul_comm] using hone 0
    | succ n ih =>
      calc
        _ ≤ γ*‖u (n+1)‖ + D*γ^(n+1) := hone (n+1)
        _ ≤ γ*(‖u 0‖*γ^(n+1) + ((n : ℝ)+1)*D*γ^n) + D*γ^(n+1) := by gcongr
        _ = _ := by simp only [Nat.cast_add, Nat.cast_one, pow_succ]; ring
  have hp : Tendsto (fun n : ℕ => γ^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ1
  have hnp : Tendsto (fun n : ℕ => (n : ℝ)*γ^n) atTop (𝓝 0) :=
    tendsto_self_mul_const_pow_of_lt_one hγ0 hγ1
  have hlim : Tendsto (fun n : ℕ => ‖u 0‖*γ^(n+1) + ((n : ℝ)+1)*D*γ^n)
      atTop (𝓝 0) := by
    have hh := ((hp.mul_const γ).const_mul ‖u 0‖).add ((hnp.add hp).mul_const D)
    convert hh using 1
    · funext n
      simp only [pow_succ]
      ring
    · simp
  exact (tendsto_add_atTop_iff_nat 1).mp (squeeze_zero_norm hbound hlim)

/-- Article: eq:quad. Use: every actual stable scalar recurrence converges to zero. -/
theorem scalar_recurrence_tendsto_zero (u : ℕ → ℝ) {a β : ℝ}
    (hβ : 0 ≤ β) (hβ1 : β < 1) (ha : |a| < 1+β)
    (hrec : ∀ n, u (n+2)=a*u (n+1)-β*u n) : Tendsto u atTop (𝓝 0) := by
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq
    ((a : ℂ)^2-4*(β : ℂ)) (n := 2) (by norm_num)
  let r : ℂ := ((a : ℂ)+d)/2
  let s : ℂ := ((a : ℂ)-d)/2
  have hr : r^2-(a : ℂ)*r+(β : ℂ)=0 := by
    dsimp [r]
    linear_combination hd/4
  have hs : s^2-(a : ℂ)*s+(β : ℂ)=0 := by
    dsimp [s]
    linear_combination hd/4
  have hrs : r+s=(a : ℂ) := by dsimp [r,s]; ring
  have hprod : r*s=(β : ℂ) := by
    dsimp [r,s]
    linear_combination -hd/4
  have hlim := recurrence_tendsto_zero_of_roots (fun n => (u n : ℂ)) r s
    (quadratic_root_norm_lt_one hβ hβ1 ha hr) (quadratic_root_norm_lt_one hβ hβ1 ha hs)
    (fun n => by rw [hrs,hprod]; exact_mod_cast hrec n)
  simpa only [Function.comp_def, Complex.ofReal_re, Complex.zero_re] using
    Complex.continuous_re.continuousAt.tendsto.comp hlim

/-- Article: eq:quad. Use: the from-rest scalar heavy-ball executor genuinely converges.
Proof: its implemented recurrence has the characteristic coefficient of the source. -/
theorem scalar_quadratic_converges {μ L α β lam : ℝ} (hμ : 0 < μ) (hα : 0 < α)
    (hβ : 0 ≤ β) (hβ1 : β < 1) (hlam : μ ≤ lam) (hlamL : lam ≤ L)
    (hquad : α*L < 2*(1+β)) (x₀ : ℝ) :
    Tendsto (iterate (fun x : ℝ => lam*x) α β x₀) atTop (𝓝 0) := by
  apply scalar_recurrence_tendsto_zero _ hβ hβ1
    (curvature_abs_lt hμ hα hlam hlamL hquad)
  intro n
  rw [iterate_recurrence]
  simp only [smul_eq_mul]
  ring

end
end polyak.Dynamics
