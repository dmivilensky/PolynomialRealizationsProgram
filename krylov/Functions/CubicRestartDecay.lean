import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
Article: main_krylov, prop:Fcycle(ii), actual cubic cycle order.
Use: convert the proved eventual cubic recurrence and convergence of the
actual restart errors into an explicit doubly exponential tail estimate.
Source: the elementary rescaled-error induction underlying R-order; see
Ortega and Rheinboldt (1970), as cited in the article. No order or rate
is assumed in addition to the established recurrence and convergence.
-/
namespace krylov.Functions
noncomputable section
open Filter Topology

/-- An eventual cubic recursion has an explicit cubic R-order tail.
Applied to the actual restarted RFC-F errors, this turns the native
cycle estimate into the article's convergence-order statement, including
eventually stationary sequences. Article: main_krylov, prop:Fcycle(ii). -/
theorem cubic_restart_decay (e : ℕ → ℝ) (he : ∀ c,0≤e c)
    (hconv : Tendsto e atTop (𝓝 0))
    (hrec : ∃ C : ℝ,0<C ∧ ∀ᶠ c in atTop,e (c+1)≤C*(e c)^3) :
    ∃ N : ℕ,∃ M : ℝ,0<M ∧ ∀ j : ℕ,e (N+j)≤M*(1/2:ℝ)^(3^j) := by
  obtain ⟨C,hC,hrec⟩ := hrec
  let K := C+1
  have hK : 0<K := by dsimp only [K]; positivity
  have hKC : K*C≤K^3 := by dsimp only [K]; nlinarith only [hC,sq_nonneg C]
  have hsmall : ∀ᶠ c in atTop,e c<(1/2:ℝ)/K :=
    hconv.eventually (gt_mem_nhds (div_pos (by norm_num) hK))
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hrec.and hsmall)
  have hscaled (j : ℕ) : K*e (N+j)≤(1/2:ℝ)^(3^j) := by
    induction j with
    | zero =>
      have hh := (lt_div_iff₀ hK).mp (hN N le_rfl).2
      simpa only [Nat.add_zero,pow_zero,pow_one,mul_comm] using hh.le
    | succ j hj =>
      have hc := (hN (N+j) (Nat.le_add_right _ _)).1
      have hp := pow_le_pow_left₀ (mul_nonneg hK.le (he _)) hj 3
      calc
        K*e (N+(j+1))≤K*(C*(e (N+j))^3) := by
          simpa only [Nat.add_assoc] using mul_le_mul_of_nonneg_left hc hK.le
        _ ≤ K^3*(e (N+j))^3 := by
          have hh := mul_le_mul_of_nonneg_right hKC (pow_nonneg (he (N+j)) 3)
          simpa only [mul_assoc] using hh
        _ = (K*e (N+j))^3 := (mul_pow _ _ _).symm
        _ ≤ ((1/2:ℝ)^(3^j))^3 := hp
        _ = (1/2:ℝ)^(3^(j+1)) := by rw [←pow_mul,pow_succ]
  refine ⟨N,K⁻¹,inv_pos.mpr hK,?_⟩
  intro j
  have hh := div_le_div_of_nonneg_right (hscaled j) hK.le
  calc
    e (N+j)=(K*e (N+j))/K := by field_simp
    _ ≤ ((1/2:ℝ)^(3^j))/K := hh
    _ = K⁻¹*(1/2:ℝ)^(3^j) := by ring

end
end krylov.Functions
