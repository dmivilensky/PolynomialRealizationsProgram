import nesterov.Stationary.Model
import nesterov.Momentum.Execution

/-!
Article: Definition `def:slm`, `eq:Muv`, and `rem:twostep`.
Use: the actual two-step executor is an instance of the general latent method;
the source coefficients retain their signs and ascending-power convention.
-/
namespace nesterov.Momentum
noncomputable section
open scoped BigOperators

/-- The source family as a stationary method; only the explicitness condition
`h≠0` is needed for this algebraic dictionary. -/
def method (β τ h : ℝ) (hh : h ≠ 0) : StationaryMethod where
  memory := 2
  memory_pos := by norm_num
  queryCoeff := ![-τ, 1+τ]
  recurrenceCoeff := ![-β/h, (1+β)/h, -1/h]
  query_sum := by simp [Fin.sum_univ_two]
  recurrence_sum := by simp [Fin.sum_univ_succ]; ring
  leading_ne := by simp [Fin.last, hh]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Latent indexing: `w₀=x₋₁` and `wₖ₊₁=xₖ`. -/
def history (g : E → E) (β τ h : ℝ) (a b : E) : ℕ → E
  | 0 => a
  | n+1 => (state g β τ h a b n).2

@[simp] theorem history_zero (g : E → E) (β τ h : ℝ) (a b : E) :
    history g β τ h a b 0 = a := rfl
@[simp] theorem history_one (g : E → E) (β τ h : ℝ) (a b : E) :
    history g β τ h a b 1 = b := rfl

theorem history_eq_fst (g : E → E) (β τ h : ℝ) (a b : E) (n : ℕ) :
    history g β τ h a b n = (state g β τ h a b n).1 := by
  cases n <;> rfl

theorem history_recurrence (g : E → E) (β τ h : ℝ) (a b : E) (n : ℕ) :
    history g β τ h a b (n+2) = history g β τ h a b (n+1) +
      β • (history g β τ h a b (n+1)-history g β τ h a b n) -
      h • g (history g β τ h a b (n+1) +
        τ • (history g β τ h a b (n+1)-history g β τ h a b n)) := by
  rw [history_eq_fst g β τ h a b n]
  rfl

theorem method_query (β τ h : ℝ) (hh : h ≠ 0) (w : ℕ → E) (n : ℕ) :
    (method β τ h hh).query w n = w (n+1)+τ • (w (n+1)-w n) := by
  change (∑ j : Fin 2, ![-τ,1+τ] j • w (n+j)) = _
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.val_zero, Fin.val_one, Nat.add_zero]
  module

/-- Equivalence with the literal source recurrence, on arbitrary trajectories. -/
theorem method_trajectory_iff (g : E → E) (β τ h : ℝ) (hh : h ≠ 0) (w : ℕ → E) :
    (method β τ h hh).IsTrajectory g w ↔ ∀ n,
      w (n+2) = w (n+1)+β • (w (n+1)-w n) -
        h • g (w (n+1)+τ • (w (n+1)-w n)) := by
  simp only [StationaryMethod.IsTrajectory, method_query]
  have hsum (n : ℕ) :
      (∑ j : Fin ((method β τ h hh).memory+1),
        (method β τ h hh).recurrenceCoeff j • w (n+j)) =
      (-β/h) • w n + ((1+β)/h) • w (n+1) + (-1/h) • w (n+2) := by
    change (∑ j : Fin 3, ![-β/h,(1+β)/h,-1/h] j • w (n+j)) = _
    simp [Fin.sum_univ_three, add_assoc]
  simp only [hsum]
  constructor
  · intro hrec n
    have hm := congrArg (fun x : E => h • x) (hrec n)
    simp only [smul_add, smul_smul] at hm
    simp only [mul_div_cancel₀ _ hh] at hm
    linear_combination (norm := module) -hm
  · intro hrec n
    apply smul_right_injective E hh
    simp only [smul_add, smul_smul, mul_div_cancel₀ _ hh]
    rw [hrec n]
    module

theorem history_isTrajectory (g : E → E) (β τ h : ℝ) (hh : h ≠ 0) (a b : E) :
    (method β τ h hh).IsTrajectory g (history g β τ h a b) :=
  (method_trajectory_iff g β τ h hh _).2 (history_recurrence g β τ h a b)

theorem method_query_history (g : E → E) (β τ h : ℝ) (hh : h ≠ 0)
    (a b : E) (n : ℕ) :
    (method β τ h hh).query (history g β τ h a b) n =
      query τ (state g β τ h a b n) := by
  rw [method_query, history_eq_fst g β τ h a b n]
  rfl

/-- Every scalar memory-two method has the article's algebraic coefficients.
The domain restrictions β∈[0,1), τ≥0, h>0 are additional tuning assumptions. -/
theorem two_step_coefficients (M : StationaryMethod) (hD : M.memory = 2) :
    ∃ β τ h : ℝ, h ≠ 0 ∧
      (∀ j : Fin 2, M.queryCoeff (Fin.cast hD.symm j) = ![-τ,1+τ] j) ∧
      (∀ j : Fin 3, M.recurrenceCoeff (Fin.cast (congrArg (·+1) hD).symm j) =
        ![-β/h,(1+β)/h,-1/h] j) := by
  rcases M with ⟨D,hpos,u,v,hu,hs,hv⟩
  change D = 2 at hD
  subst D
  dsimp only at *
  let h : ℝ := -1 / v 2
  let β : ℝ := v 0 / v 2
  let τ : ℝ := - u 0
  have hv' : v 2 ≠ 0 := hv
  have hh : h ≠ 0 := by dsimp [h]; exact div_ne_zero (by norm_num) hv'
  refine ⟨β, τ, h, hh, ?_, ?_⟩
  · intro j
    simp only [Fin.sum_univ_two] at hu
    fin_cases j
    all_goals simp [τ]
    all_goals linarith
  · intro j
    change (∑ j : Fin 3, v j) = 0 at hs
    rw [Fin.sum_univ_three] at hs
    fin_cases j
    all_goals simp [β, h]
    all_goals field_simp [hv']
    all_goals nlinarith

end
end nesterov.Momentum
