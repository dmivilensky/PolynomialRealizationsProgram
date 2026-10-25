import polyak.Dynamics.Iteration
import polyak.Dynamics.Tuning

/-!
Article: polyaksiopt, Lemma normalization, eq:normrec.
Use: conjugate the actual from-rest executor by translation to the minimizer.
-/

namespace polyak.Dynamics
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Article: eq:normrec. Use: one normalized step with current/previous errors. -/
def normalizedStep (σ : E → E) (A B β : ℝ) (p : E × E) : E × E :=
  (A • p.1 + B • σ p.1 - β • p.2, p.1)

/-- Article: eq:normrec. Use: normalized two-position executor with zero momentum. -/
def normalizedState (σ : E → E) (A B β : ℝ) (e₀ : E) : ℕ → E × E
  | 0 => (e₀, e₀)
  | n+1 => normalizedStep σ A B β (normalizedState σ A B β e₀ n)

/-- Article: eq:hb. Use: translation of the actual executor does not change momentum. -/
theorem iterate_translate (g h : E → E) (a : E) (α β : ℝ)
    (hg : ∀ e, g (a+e) = h e) (e₀ : E) (n : ℕ) :
    iterate g α β (a+e₀) n = a + iterate h α β e₀ n := by
  have hs : ∀ n, state g α β (a+e₀) n =
      (a+(state h α β e₀ n).1, a+(state h α β e₀ n).2) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [state, ih, step, hg]
      congr 1
      module
  exact congrArg Prod.fst (hs n)

/-- Article: lem:normalization. Use: exact error-state identity for the genuine executor.
Proof: substitute the actual gradient dictionary into a single step, then induct. -/
theorem normalized_error_state (g σ : E → E) (μ L α β : ℝ) (a e₀ : E)
    (hg : ∀ e, g (a+e) = ((L+μ)/2) • e - ((L-μ)/2) • σ e) (n : ℕ) :
    ((state g α β (a+e₀) n).1-a, (state g α β (a+e₀) n).2-a) =
      normalizedState σ (normalizedA μ L α β) (normalizedB μ L α) β e₀ n := by
  have hs : ∀ n, state g α β (a+e₀) n =
      (a+(normalizedState σ (normalizedA μ L α β) (normalizedB μ L α) β e₀ n).1,
       a+(normalizedState σ (normalizedA μ L α β) (normalizedB μ L α) β e₀ n).2) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [state, normalizedState, ih, step, normalizedStep, hg,
        normalizedA, normalizedB]
      congr 1
      module
  rw [hs n]
  simp

/-- Article: lem:normalization. Use: the Polyak normalized executor has A=0 and B=2q. -/
theorem polyak_error_state (g σ : E → E) {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (a e₀ : E)
    (hg : ∀ e, g (a+e) = ((L+μ)/2) • e - ((L-μ)/2) • σ e) (n : ℕ) :
    ((state g (polyakAlpha μ L) (polyakBeta μ L) (a+e₀) n).1-a,
      (state g (polyakAlpha μ L) (polyakBeta μ L) (a+e₀) n).2-a) =
      normalizedState σ 0 (2*polyakQ μ L) (polyakQ μ L ^ 2) e₀ n := by
  have h := normalized_error_state g σ μ L (polyakAlpha μ L) (polyakBeta μ L) a e₀ hg n
  rw [polyak_normalizedA hμ hL, polyak_normalizedB hμ hL] at h
  exact h

end
end polyak.Dynamics
