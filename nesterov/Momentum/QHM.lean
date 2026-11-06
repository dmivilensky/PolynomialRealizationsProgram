import nesterov.Momentum.Execution

/-!
Article: `rem:twostep` and the initialization convention used by corollaries
`cor:B` and `cor:QHM`.
Use: QHM is executed with its own accumulator; the equality with extrapolated
queries is proved from both actual recurrences and their actual first step.
-/
namespace nesterov.Momentum
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- State order is previous accumulator and current QHM iterate. -/
def qhmStep (g : E → E) (α β ν : ℝ) (p : E × E) : E × E :=
  let d := β • p.1 + (1-β) • g p.2
  (d, p.2 - α • ((1-ν) • g p.2 + ν • d))

/-- The usual QHM initialization is exactly `d₋₁=0`. -/
def qhmState (g : E → E) (α β ν : ℝ) (x₀ : E) : ℕ → E × E
  | 0 => (0,x₀)
  | n+1 => qhmStep g α β ν (qhmState g α β ν x₀ n)

def qhmIterate (g : E → E) (α β ν : ℝ) (x₀ : E) (n : ℕ) : E :=
  (qhmState g α β ν x₀ n).2

@[simp] theorem qhmIterate_zero (g : E → E) (α β ν : ℝ) (x₀ : E) :
    qhmIterate g α β ν x₀ 0 = x₀ := rfl

theorem qhmIterate_one (g : E → E) (α β ν : ℝ) (x₀ : E) :
    qhmIterate g α β ν x₀ 1 = x₀ - (α*(1-ν*β)) • g x₀ := by
  simp only [qhmIterate, qhmState, qhmStep, smul_zero, zero_add]
  module

/-- Elimination of the accumulator, retaining both gradient calls. -/
theorem qhmIterate_recurrence (g : E → E) (α β ν : ℝ) (x₀ : E) (n : ℕ) :
    qhmIterate g α β ν x₀ (n+2) = qhmIterate g α β ν x₀ (n+1) +
      β • (qhmIterate g α β ν x₀ (n+1)-qhmIterate g α β ν x₀ n) -
      (α*(1-ν*β)) • g (qhmIterate g α β ν x₀ (n+1)) +
      (α*(1-ν)*β) • g (qhmIterate g α β ν x₀ n) := by
  simp only [qhmIterate, qhmState, qhmStep]
  module

def qhmExtrapolation (β ν : ℝ) : ℝ := (1-ν)*β/(1-β)

theorem qhm_coefficients (α β ν : ℝ) (hβ : β ≠ 1) :
    (α*(1-β))*(1+qhmExtrapolation β ν) = α*(1-ν*β) ∧
    (α*(1-β))*qhmExtrapolation β ν = α*(1-ν)*β := by
  have hb : 1-β ≠ 0 := sub_ne_zero.mpr (Ne.symm hβ)
  constructor
  · dsimp [qhmExtrapolation]
    field_simp [hb]
    ring
  · dsimp [qhmExtrapolation]
    field_simp [hb]

/-- QHM iterates are exactly the source method's queries from rest, for every
horizon and every oracle. No asymptotic or quadratic assumption is used. -/
theorem qhmIterate_eq_queries (g : E → E) (α β ν : ℝ) (hβ : β ≠ 1)
    (x₀ : E) (n : ℕ) :
    qhmIterate g α β ν x₀ n =
      queryIterate g β (qhmExtrapolation β ν) (α*(1-β)) x₀ n := by
  obtain ⟨hc₁,hc₂⟩ := qhm_coefficients α β ν hβ
  have he : ∀ n, qhmIterate g α β ν x₀ n =
      queryIterate g β (qhmExtrapolation β ν) (α*(1-β)) x₀ n ∧
      qhmIterate g α β ν x₀ (n+1) =
      queryIterate g β (qhmExtrapolation β ν) (α*(1-β)) x₀ (n+1) := by
    intro n
    induction n with
    | zero => simp [qhmIterate_one, queryIterate_one, hc₁]
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [qhmIterate_recurrence, queryIterate_recurrence, hc₁, hc₂, ih.1, ih.2]
  exact (he n).1

theorem qhm_parameters_admissible {α β ν : ℝ} (hα : 0 < α)
    (hβ₀ : 0 ≤ β) (hβ₁ : β < 1) (hν : ν ≤ 1) :
    0 < α*(1-β) ∧ 0 ≤ qhmExtrapolation β ν := by
  exact ⟨mul_pos hα (sub_pos.mpr hβ₁),
    div_nonneg (mul_nonneg (sub_nonneg.mpr hν) hβ₀) (sub_pos.mpr hβ₁).le⟩

@[simp] theorem qhmExtrapolation_one (β : ℝ) : qhmExtrapolation β 1 = 0 := by
  simp [qhmExtrapolation]

theorem qhmExtrapolation_self (β : ℝ) (hβ : β ≠ 1) :
    qhmExtrapolation β β = β := by
  dsimp [qhmExtrapolation]
  exact mul_div_cancel_left₀ β (sub_ne_zero.mpr (Ne.symm hβ))

end
end nesterov.Momentum
