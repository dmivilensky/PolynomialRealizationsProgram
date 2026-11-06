import polyak.Dynamics.Iteration

/-!
Article: `eq:M`, `rem:twostep`, and Appendix A.
Use: the actual momentum executor, with previous/current state order and
the gradient evaluated at the extrapolated query. Parameters are unrestricted
here; positivity assumptions are imposed only by the theorems that use them.
-/
namespace nesterov.Momentum
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The source query, in previous/current state coordinates. -/
def query (τ : ℝ) (p : E × E) : E := p.2 + τ • (p.2 - p.1)

/-- One physical gradient call and the actual memory shift. -/
def step (g : E → E) (β τ h : ℝ) (p : E × E) : E × E :=
  (p.2, p.2 + β • (p.2 - p.1) - h • g (query τ p))

/-- Arbitrary initial memory, with no supplied trajectory. -/
def state (g : E → E) (β τ h : ℝ) (xprev xcur : E) : ℕ → E × E
  | 0 => (xprev, xcur)
  | n + 1 => step g β τ h (state g β τ h xprev xcur n)

/-- The prescribed zero-momentum initialization `x₋₁=x₀`. -/
def restState (g : E → E) (β τ h : ℝ) (x₀ : E) : ℕ → E × E :=
  state g β τ h x₀ x₀

/-- The actual iterate `xₙ` from rest. -/
def iterate (g : E → E) (β τ h : ℝ) (x₀ : E) (n : ℕ) : E :=
  (restState g β τ h x₀ n).2

/-- The actual gradient query `x̃ₙ` from rest. -/
def queryIterate (g : E → E) (β τ h : ℝ) (x₀ : E) (n : ℕ) : E :=
  query τ (restState g β τ h x₀ n)

@[simp] theorem query_zero (p : E × E) : query 0 p = p.2 := by simp [query]
@[simp] theorem state_zero (g : E → E) (β τ h : ℝ) (a b : E) :
    state g β τ h a b 0 = (a,b) := rfl
@[simp] theorem state_succ_fst (g : E → E) (β τ h : ℝ) (a b : E) (n : ℕ) :
    (state g β τ h a b (n+1)).1 = (state g β τ h a b n).2 := rfl
@[simp] theorem iterate_zero (g : E → E) (β τ h : ℝ) (x₀ : E) :
    iterate g β τ h x₀ 0 = x₀ := rfl
@[simp] theorem queryIterate_zero (g : E → E) (β τ h : ℝ) (x₀ : E) :
    queryIterate g β τ h x₀ 0 = x₀ := by simp [queryIterate, restState, state, query]
@[simp] theorem iterate_one (g : E → E) (β τ h : ℝ) (x₀ : E) :
    iterate g β τ h x₀ 1 = x₀ - h • g x₀ := by
  simp [iterate, restState, state, step, query]

theorem iterate_recurrence (g : E → E) (β τ h : ℝ) (x₀ : E) (n : ℕ) :
    iterate g β τ h x₀ (n+2) = iterate g β τ h x₀ (n+1) +
      β • (iterate g β τ h x₀ (n+1) - iterate g β τ h x₀ n) -
      h • g (queryIterate g β τ h x₀ (n+1)) := rfl

theorem queryIterate_succ (g : E → E) (β τ h : ℝ) (x₀ : E) (n : ℕ) :
    queryIterate g β τ h x₀ (n+1) = iterate g β τ h x₀ (n+1) +
      τ • (iterate g β τ h x₀ (n+1) - iterate g β τ h x₀ n) := rfl

theorem queryIterate_one (g : E → E) (β τ h : ℝ) (x₀ : E) :
    queryIterate g β τ h x₀ 1 = x₀ - (h*(1+τ)) • g x₀ := by
  rw [queryIterate_succ, iterate_one, iterate_zero]
  module

/-- Source gradient-correction equation, with its actual first query. -/
theorem queryIterate_recurrence (g : E → E) (β τ h : ℝ) (x₀ : E) (n : ℕ) :
    queryIterate g β τ h x₀ (n+2) = queryIterate g β τ h x₀ (n+1) +
      β • (queryIterate g β τ h x₀ (n+1) - queryIterate g β τ h x₀ n) -
      (h*(1+τ)) • g (queryIterate g β τ h x₀ (n+1)) +
      (h*τ) • g (queryIterate g β τ h x₀ n) := by
  cases n with
  | zero =>
    rw [queryIterate_succ, iterate_recurrence, queryIterate_one,
      queryIterate_zero, iterate_one, iterate_zero]
    module
  | succ n =>
    rw [queryIterate_succ, iterate_recurrence]
    rw [queryIterate_succ g β τ h x₀ n, queryIterate_succ g β τ h x₀ (n+1)]
    rw [iterate_recurrence g β τ h x₀ n]
    simp only [queryIterate_succ]
    module

/-- Every point with zero gradient is a fixed state. -/
theorem state_stationary (g : E → E) (β τ h : ℝ) (a : E) (ha : g a = 0)
    (n : ℕ) : state g β τ h a a n = (a,a) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [state, ih, step, query, ha]

/-- The τ=0 executor is the existing Polyak executor, including initialization. -/
theorem restState_heavyBall (g : E → E) (β h : ℝ) (x₀ : E) (n : ℕ) :
    restState g β 0 h x₀ n = (polyak.Dynamics.state g h β x₀ n).swap := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change step g β 0 h (restState g β 0 h x₀ n) = _
    rw [ih]
    simp only [step, query_zero, polyak.Dynamics.state, polyak.Dynamics.step,
      Prod.swap]
    congr 1
    module

theorem iterate_heavyBall (g : E → E) (β h : ℝ) (x₀ : E) (n : ℕ) :
    iterate g β 0 h x₀ n = polyak.Dynamics.iterate g h β x₀ n := by
  simp [iterate, restState_heavyBall, polyak.Dynamics.iterate]

end
end nesterov.Momentum
