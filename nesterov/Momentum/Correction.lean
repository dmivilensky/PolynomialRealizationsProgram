import nesterov.Momentum.Execution
import Mathlib.Tactic.Module

/-!
Article: Remark two-step methods and Appendix A.
Use: arbitrary gradient-correction histories are exactly the query histories
of momentum when the source determinant is nonzero. Initial memories are free.
-/

noncomputable section
namespace nesterov.Momentum
namespace Correction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def determinant (β τ : ℝ) : ℝ := (1 + τ) * β - τ

/-- The gradient-correction state stores consecutive gradient queries. -/
def step (g : E → E) (β τ h : ℝ) (q : E × E) : E × E :=
  (q.2, q.2 + β • (q.2 - q.1) - (h * (1 + τ)) • g q.2 + (h * τ) • g q.1)

def state (g : E → E) (β τ h : ℝ) (a b : E) : ℕ → E × E
  | 0 => (a,b)
  | n+1 => step g β τ h (state g β τ h a b n)

/-- Both coordinates are actual consecutive queries of the source method. -/
def queryState (g : E → E) (β τ h : ℝ) (p : E × E) : E × E :=
  (Momentum.query τ p, Momentum.query τ (Momentum.step g β τ h p))

/-- The affine gradient term restores the linear invertible memory map. -/
def inverseState (g : E → E) (β τ h : ℝ) (q : E × E) : E × E :=
  ((determinant β τ)⁻¹ • ((1 + (1 + τ) * β) • q.1 -
      (1 + τ) • (q.2 + ((1 + τ) * h) • g q.1)),
    (determinant β τ)⁻¹ • (((1 + τ) * β) • q.1 -
      τ • (q.2 + ((1 + τ) * h) • g q.1)))

theorem queryState_step (g : E → E) (β τ h : ℝ) (p : E × E) :
    queryState g β τ h (Momentum.step g β τ h p) = step g β τ h (queryState g β τ h p) := by
  apply Prod.ext
  · rfl
  · simp only [queryState, step, Momentum.query, Momentum.step]
    module

theorem query_inverseState (g : E → E) (β τ h : ℝ)
    (hδ : determinant β τ ≠ 0) (q : E × E) :
    Momentum.query τ (inverseState g β τ h q) = q.1 := by
  calc
    _ = (determinant β τ)⁻¹ • (determinant β τ • q.1) := by
      unfold inverseState Momentum.query determinant
      module
    _ = q.1 := by rw [smul_smul, inv_mul_cancel₀ hδ, one_smul]

theorem corrected_next_query (g : E → E) (β τ h : ℝ) (p : E × E) :
    Momentum.query τ (Momentum.step g β τ h p) + ((1 + τ) * h) • g (Momentum.query τ p) =
      (1 + (1 + τ) * β) • p.2 - ((1 + τ) * β) • p.1 := by
  simp only [Momentum.query, Momentum.step]
  module

theorem inverseState_queryState (g : E → E) (β τ h : ℝ)
    (hδ : determinant β τ ≠ 0) (p : E × E) :
    inverseState g β τ h (queryState g β τ h p) = p := by
  have hR := corrected_next_query g β τ h p
  apply Prod.ext
  · change (determinant β τ)⁻¹ •
      ((1 + (1 + τ) * β) • Momentum.query τ p - (1 + τ) •
        (Momentum.query τ (Momentum.step g β τ h p) + ((1 + τ) * h) • g (Momentum.query τ p))) = p.1
    rw [hR]
    calc
      _ = (determinant β τ)⁻¹ • (determinant β τ • p.1) := by unfold determinant Momentum.query; module
      _ = _ := by rw [smul_smul, inv_mul_cancel₀ hδ, one_smul]
  · change (determinant β τ)⁻¹ •
      (((1 + τ) * β) • Momentum.query τ p - τ •
        (Momentum.query τ (Momentum.step g β τ h p) + ((1 + τ) * h) • g (Momentum.query τ p))) = p.2
    rw [hR]
    calc
      _ = (determinant β τ)⁻¹ • (determinant β τ • p.2) := by unfold determinant Momentum.query; module
      _ = _ := by rw [smul_smul, inv_mul_cancel₀ hδ, one_smul]

theorem queryState_inverseState (g : E → E) (β τ h : ℝ)
    (hδ : determinant β τ ≠ 0) (q : E × E) :
    queryState g β τ h (inverseState g β τ h q) = q := by
  have hq := query_inverseState g β τ h hδ q
  have hR := corrected_next_query g β τ h (inverseState g β τ h q)
  apply Prod.ext
  · exact hq
  · have hlinear : (1 + (1 + τ) * β) • (inverseState g β τ h q).2 -
        ((1 + τ) * β) • (inverseState g β τ h q).1 = q.2 + ((1 + τ) * h) • g q.1 := by
      calc
        _ = (determinant β τ)⁻¹ •
            (determinant β τ • (q.2 + ((1 + τ) * h) • g q.1)) := by
          unfold inverseState determinant
          module
        _ = _ := by rw [smul_smul, inv_mul_cancel₀ hδ, one_smul]
    change Momentum.query τ (Momentum.step g β τ h (inverseState g β τ h q)) = q.2
    rw [hq, hlinear] at hR
    linear_combination (norm := module) hR

/-- An explicit bijection of physical states, including the gradient term. -/
def stateEquiv (g : E → E) (β τ h : ℝ) (hδ : determinant β τ ≠ 0) : (E × E) ≃ (E × E) where
  toFun := queryState g β τ h
  invFun := inverseState g β τ h
  left_inv := inverseState_queryState g β τ h hδ
  right_inv := queryState_inverseState g β τ h hδ

/-- Every correction executor corresponds to one momentum executor. -/
theorem state_conjugacy (g : E → E) (β τ h : ℝ) (p : E × E) (n : ℕ) :
    queryState g β τ h (Momentum.state g β τ h p.1 p.2 n) =
      state g β τ h (queryState g β τ h p).1 (queryState g β τ h p).2 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change queryState g β τ h (Momentum.step g β τ h (Momentum.state g β τ h p.1 p.2 n)) = _
    rw [queryState_step, ih]
    rfl

theorem state_from_inverse (g : E → E) (β τ h : ℝ)
    (hδ : determinant β τ ≠ 0) (q : E × E) (n : ℕ) :
    state g β τ h q.1 q.2 n = queryState g β τ h
      (Momentum.state g β τ h (inverseState g β τ h q).1 (inverseState g β τ h q).2 n) := by
  rw [state_conjugacy, queryState_inverseState g β τ h hδ]

def IsTrajectory (g : E → E) (β τ h : ℝ) (w : ℕ → E) : Prop :=
  ∀ n, w (n+2) = w (n+1) + β • (w (n+1)-w n) -
    (h*(1+τ)) • g (w (n+1)) + (h*τ) • g (w n)

theorem IsTrajectory.eq_state {g : E → E} {β τ h : ℝ} {w : ℕ → E}
    (hw : IsTrajectory g β τ h w) (n : ℕ) :
    state g β τ h (w 0) (w 1) n = (w n,w (n+1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change step g β τ h (state g β τ h (w 0) (w 1) n) = _
    rw [ih]
    change (w (n+1),w (n+1)+β • (w (n+1)-w n)-
      (h*(1+τ)) • g (w (n+1))+(h*τ) • g (w n)) = _
    rw [← hw n]

/-- Every arbitrary correction trajectory has a unique source momentum memory. -/
theorem IsTrajectory.existsUnique_query_history {g : E → E} {β τ h : ℝ} {w : ℕ → E}
    (hw : IsTrajectory g β τ h w) (hδ : determinant β τ ≠ 0) :
    ∃! p : E × E, ∀ n, queryState g β τ h (Momentum.state g β τ h p.1 p.2 n) =
      (w n,w (n+1)) := by
  refine ⟨inverseState g β τ h (w 0,w 1), ?_, ?_⟩
  · intro n
    rw [← state_from_inverse g β τ h hδ, hw.eq_state]
  · intro p hp
    have he := hp 0
    change queryState g β τ h p = (w 0,w 1) at he
    rw [← he, inverseState_queryState g β τ h hδ]

/-- The exceptional tuning is exactly the zero determinant in the source. -/
theorem determinant_ne_zero_iff {β τ : ℝ} (hτ : 0 ≤ τ) :
    determinant β τ ≠ 0 ↔ β ≠ τ / (1 + τ) := by
  have hm : 1 + τ ≠ 0 := by positivity
  rw [ne_eq, ne_eq, eq_div_iff hm]
  unfold determinant
  constructor
  · intro hn he
    apply hn
    nlinarith
  · intro hn he
    apply hn
    nlinarith

/-- The source conversion from two gradient coefficients is exact. -/
theorem step_gradient_coefficients (g : E → E) (β h₁ h₂ : ℝ)
    (hh : h₁ - h₂ ≠ 0) (q : E × E) :
    step g β (h₂ / (h₁-h₂)) (h₁-h₂) q =
      (q.2, q.2 + β • (q.2-q.1) - h₁ • g q.2 + h₂ • g q.1) := by
  have hfirst : (h₁-h₂) * (1 + h₂/(h₁-h₂)) = h₁ := by field_simp; ring
  have hsecond : (h₁-h₂) * (h₂/(h₁-h₂)) = h₂ := mul_div_cancel₀ _ hh
  simp only [step, hfirst, hsecond]

/-- Autonomy makes every restart another actual correction execution. -/
theorem state_add (g : E → E) (β τ h : ℝ) (a b : E) (k n : ℕ) :
    state g β τ h a b (k+n) = state g β τ h
      (state g β τ h a b k).1 (state g β τ h a b k).2 n := by
  induction n with
  | zero => simp only [Nat.add_zero, state]
  | succ n ih =>
    change step g β τ h (state g β τ h a b (k+n)) =
      step g β τ h (state g β τ h (state g β τ h a b k).1 (state g β τ h a b k).2 n)
    rw [ih]

/-- Translating the minimizer preserves the physical correction execution. -/
theorem state_center (g : E → E) (β τ h : ℝ) (a b c : E) (n : ℕ) :
    state (fun x => g (c+x)) β τ h (a-c) (b-c) n =
      ((state g β τ h a b n).1-c, (state g β τ h a b n).2-c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change step (fun x => g (c+x)) β τ h
      (state (fun x => g (c+x)) β τ h (a-c) (b-c) n) = _
    rw [ih]
    change step (fun x => g (c+x)) β τ h
      ((state g β τ h a b n).1-c, (state g β τ h a b n).2-c) =
      ((step g β τ h (state g β τ h a b n)).1-c,
        (step g β τ h (state g β τ h a b n)).2-c)
    have hcancel (x : E) : c+(x-c)=x := by abel
    simp only [step, hcancel]
    apply Prod.ext
    · rfl
    · module

end Correction
end nesterov.Momentum
