import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

/-!
Article: polyaksiopt, introduction, eq:hb and eq:normrec.
Use: define the actual heavy-ball executor from rest and prove its exact
recurrence and dimension-independent finite-horizon bounds.
-/

namespace polyak.Dynamics
noncomputable section
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Article: eq:hb. Use: one actual step, with current and previous positions. -/
def step (g : E → E) (α β : ℝ) (p : E × E) : E × E :=
  (p.1 - α • g p.1 + β • (p.1 - p.2), p.1)

/-- Article: eq:hb. Use: the two-position state with the prescribed zero momentum. -/
def state (g : E → E) (α β : ℝ) (x₀ : E) : ℕ → E × E
  | 0 => (x₀, x₀)
  | n + 1 => step g α β (state g α β x₀ n)

/-- Article: eq:hb. Use: actual positions of the heavy-ball run. -/
def iterate (g : E → E) (α β : ℝ) (x₀ : E) (n : ℕ) : E :=
  (state g α β x₀ n).1

/-- Article: eq:hb. Use: exact initialization, including horizon zero. -/
@[simp] theorem iterate_zero (g : E → E) (α β : ℝ) (x₀ : E) :
    iterate g α β x₀ 0 = x₀ := rfl

/-- Article: eq:hb. Use: recover the previous position from the real state. -/
@[simp] theorem state_snd_succ (g : E → E) (α β : ℝ) (x₀ : E) (n : ℕ) :
    (state g α β x₀ (n+1)).2 = iterate g α β x₀ n := rfl

/-- Article: eq:hb. Use: the first step genuinely starts with zero momentum. -/
@[simp] theorem iterate_one (g : E → E) (α β : ℝ) (x₀ : E) :
    iterate g α β x₀ 1 = x₀ - α • g x₀ := by
  simp [iterate, state, step]

/-- Article: eq:hb. Use: exact second-order recurrence for all later steps. -/
theorem iterate_recurrence (g : E → E) (α β : ℝ) (x₀ : E) (n : ℕ) :
    iterate g α β x₀ (n+2) = iterate g α β x₀ (n+1) -
      α • g (iterate g α β x₀ (n+1)) +
      β • (iterate g α β x₀ (n+1) - iterate g α β x₀ n) := rfl

/-- Article: eq:hb. Use: uniqueness of the actual executor from its source recurrence.
Proof: induction on two consecutive positions. -/
theorem iterate_unique (g : E → E) (α β : ℝ) (x₀ : E) (x : ℕ → E)
    (h₀ : x 0 = x₀) (h₁ : x 1 = x₀ - α • g x₀)
    (hrec : ∀ n, x (n+2) = x (n+1) - α • g (x (n+1)) +
      β • (x (n+1) - x n)) : x = iterate g α β x₀ := by
  funext n
  have h : ∀ n, x n = iterate g α β x₀ n ∧
      x (n+1) = iterate g α β x₀ (n+1) := by
    intro n
    induction n with
    | zero => simpa using And.intro h₀ h₁
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [hrec, iterate_recurrence, ih.1, ih.2]
  exact (h n).1

/-- Article: eq:hb. Use: the stationary point stays fixed from rest. -/
theorem iterate_stationary (g : E → E) (α β : ℝ) (xstar : E) (hg : g xstar = 0)
    (n : ℕ) : iterate g α β xstar n = xstar := by
  have h : state g α β xstar n = (xstar, xstar) := by
    induction n with
    | zero => rfl
    | succ n ih => simp [state, ih, step, hg]
  simp [iterate, h]

/-- Article: eq:WN. Use: a single state size with dimension-independent constants. -/
def errorSize (xstar : E) (p : E × E) : ℝ := max ‖p.1 - xstar‖ ‖p.2 - xstar‖

omit [NormedSpace ℝ E] in
/-- Article: eq:WN. Use: the state size is nonnegative. -/
theorem errorSize_nonneg (xstar : E) (p : E × E) : 0 ≤ errorSize xstar p :=
  (norm_nonneg _).trans (le_max_left _ _)

/-- Article: eq:WN. Use: a finite step bound for every Lipschitz gradient field.
Proof: triangle inequalities and the Lipschitz bound from the stationary point. -/
theorem errorSize_step_le {g : E → E} {L : ℝ≥0} (hg : LipschitzWith L g)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) {xstar : E} (hstar : g xstar = 0)
    (p : E × E) :
    errorSize xstar (step g α β p) ≤ (1 + α * L + 2 * β) * errorSize xstar p := by
  have hL : 0 ≤ (L : ℝ) := L.coe_nonneg
  have hp : ‖p.1 - xstar‖ ≤ errorSize xstar p := le_max_left _ _
  have hq : ‖p.2 - xstar‖ ≤ errorSize xstar p := le_max_right _ _
  have hgn : ‖g p.1‖ ≤ (L : ℝ) * ‖p.1 - xstar‖ := by
    simpa [dist_eq_norm, hstar] using hg.dist_le_mul p.1 xstar
  have hd : ‖p.1 - p.2‖ ≤ ‖p.1 - xstar‖ + ‖p.2 - xstar‖ := by
    simpa only [dist_eq_norm, norm_sub_rev xstar p.2] using dist_triangle p.1 xstar p.2
  have hs : ‖(step g α β p).1 - xstar‖ ≤
      (1 + α * L + 2 * β) * errorSize xstar p := by
    have he : (step g α β p).1 - xstar =
        (p.1 - xstar) + -(α • g p.1) + β • (p.1 - p.2) := by
      simp only [step]
      module
    rw [he]
    calc
      _ ≤ ‖p.1 - xstar‖ + ‖α • g p.1‖ + ‖β • (p.1 - p.2)‖ := by
        simpa using (norm_add_le ((p.1-xstar) + -(α • g p.1))
          (β • (p.1-p.2))).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = ‖p.1-xstar‖ + α * ‖g p.1‖ + β * ‖p.1-p.2‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hα, Real.norm_of_nonneg hβ]
      _ ≤ ‖p.1-xstar‖ + α * ((L : ℝ) * ‖p.1-xstar‖) +
          β * (‖p.1-xstar‖ + ‖p.2-xstar‖) := by gcongr
      _ ≤ errorSize xstar p + α * ((L : ℝ) * errorSize xstar p) +
          β * (errorSize xstar p + errorSize xstar p) := by gcongr
      _ = _ := by ring
  exact max_le hs (by
    have hsize := errorSize_nonneg xstar p
    dsimp [step]
    have hm := mul_nonneg (mul_nonneg hα hL) hsize
    have hb := mul_nonneg hβ hsize
    nlinarith)

/-- Article: eq:WN. Use: every finite horizon has a uniform exponential majorant. -/
theorem errorSize_state_le {g : E → E} {L : ℝ≥0} (hg : LipschitzWith L g)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) {xstar : E} (hstar : g xstar = 0)
    (x₀ : E) (n : ℕ) :
    errorSize xstar (state g α β x₀ n) ≤ (1 + α * L + 2 * β)^n * ‖x₀-xstar‖ := by
  have hK : 0 ≤ 1 + α * (L : ℝ) + 2 * β := by positivity
  induction n with
  | zero => simp [errorSize, state]
  | succ n ih =>
    exact (errorSize_step_le hg hα hβ hstar _).trans (by
      simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left ih hK)

/-- Article: eq:WN. Use: bound the genuine position rather than just its state. -/
theorem iterate_error_le {g : E → E} {L : ℝ≥0} (hg : LipschitzWith L g)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) {xstar : E} (hstar : g xstar = 0)
    (x₀ : E) (n : ℕ) :
    ‖iterate g α β x₀ n-xstar‖ ≤ (1 + α * L + 2 * β)^n * ‖x₀-xstar‖ :=
  (le_max_left _ _).trans (errorSize_state_le hg hα hβ hstar x₀ n)

end
end polyak.Dynamics
