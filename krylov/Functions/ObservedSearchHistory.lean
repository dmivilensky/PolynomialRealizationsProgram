import krylov.Methods.ExecutedFC

/-!
Article: main_krylov, lem:cycle-transfer, actual observed function histories.
Use: assemble the existing policy-history type from actual physical points,
gradients, directions and averaged operators. The exact search execution
identity is an algebraic backend; its native analytic hypotheses are proved
separately from the objective, without assuming any query bounds.
Source: the repository's actual protocol and observed secant dictionary.
-/

namespace krylov.Functions
noncomputable section
open krylov.Methods krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Assemble complete actual observed search records from the physical query data.
Article: main_krylov, lem:cycle-transfer, preservation of all native observations. -/
def observedSearchHistory (G : E → E) (A : ℕ → E →L[ℝ] E) (x d : ℕ → E) : ℕ → History E
  | 0 => ⟨G (x 0), []⟩
  | k + 1 =>
      let prev := observedSearchHistory G A x d k
      ⟨G (x 0), ⟨d k, A k (d k), x (k + 1) - x k, G (x (k + 1)), []⟩ :: prev.records⟩

/-- The initial observed gradient is exactly retained.
Article: main_krylov, lem:cycle-transfer. -/
theorem observedSearchHistory_initial (G : E → E) (A : ℕ → E →L[ℝ] E) (x d : ℕ → E) (k : ℕ) :
    (observedSearchHistory G A x d k).initial = G (x 0) := by cases k <;> rfl

/-- The current observed gradient is the true gradient at the current physical point.
Article: main_krylov, lem:cycle-transfer. -/
theorem observedSearchHistory_gradient (G : E → E) (A : ℕ → E →L[ℝ] E) (x d : ℕ → E) (k : ℕ) :
    (observedSearchHistory G A x d k).gradient = G (x k) := by cases k <;> rfl

/-- The actual record count is the actual execution clock.
Article: main_krylov, lem:cycle-transfer. -/
theorem observedSearchHistory_length (G : E → E) (A : ℕ → E →L[ℝ] E) (x d : ℕ → E) (k : ℕ) :
    (observedSearchHistory G A x d k).records.length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [observedSearchHistory, List.length_cons] using congrArg Nat.succ ih

/-- The stored pairs are precisely the actual physical steps and actual gradient differences.
Article: main_krylov, alg:fc and lem:cycle-transfer. -/
theorem observedSearchHistory_pairs (G : E → E) (A : ℕ → E →L[ℝ] E) (x d : ℕ → E) (k : ℕ) :
    (observedSearchHistory G A x d k).pairs =
      executedPairs (fun j => x (j + 1) - x j) (fun j => G (x (j + 1)) - G (x j)) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hinit := observedSearchHistory_initial G A x d k
    conv_lhs => rw [observedSearchHistory]
    rw [← hinit]
    change (x (k + 1) - x k, G (x (k + 1)) - (observedSearchHistory G A x d k).gradient) ::
      (observedSearchHistory G A x d k).pairs = _
    rw [observedSearchHistory_gradient, ih]
    rfl

/-- Genuine physical search records execute exactly the existing FC operator protocol.
Article: main_krylov, lem:cycle-transfer, algebraic execution backend.
Proof: identify the actual direction and observed search quotient at each
step, then unfold the true zero-correction protocol. -/
theorem observedSearchHistory_eq_fcHistory (G : E → E) (A : ℕ → E →L[ℝ] E) (x d : ℕ → E)
    (memory : ℕ → ℕ)
    (hd : ∀ k, (fcMethod memory).direction (observedSearchHistory G A x d k) = d k)
    (hs : ∀ k, x (k + 1) - x k = lineLength (G (x k)) (d k) (A k (d k)) • d k)
    (hg : ∀ k, G (x (k + 1)) = searchedGradient (G (x k)) (d k) (A k (d k))) :
    ∀ k : ℕ, observedSearchHistory G A x d k = fcHistory memory A (G (x 0)) k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    change observedSearchHistory G A x d (k + 1) =
      methodAdvance (fcMethod memory) (A k) (A k) (fcHistory memory A (G (x 0)) k)
    rw [← ih]
    rw [methodAdvance, hd, observedSearchHistory_gradient]
    simp only [fcMethod, retainedMethod, runCorrections, add_zero]
    rw [← hs k, ← hg k, observedSearchHistory_initial]
    rfl

end
end krylov.Functions
