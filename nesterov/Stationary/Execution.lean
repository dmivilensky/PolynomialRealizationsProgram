import nesterov.Stationary.Model

/-!
Article: Definition `def:slm`, explicit execution and Appendix A.
Use: a method determines one and only one trajectory from its memory state.
-/
namespace nesterov.StationaryMethod
noncomputable section
open scoped BigOperators
variable (M : nesterov.StationaryMethod)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The causal recursion determined by the nonzero final coefficient. -/
def run (g : E → E) (initial : Fin M.memory → E) : ℕ → E :=
  Nat.strongRec fun n rec =>
    if hn : n < M.memory then initial ⟨n, hn⟩ else
      (M.recurrenceCoeff (Fin.last M.memory))⁻¹ •
        (g (∑ j : Fin M.memory, M.queryCoeff j •
          rec (n-M.memory+j) (by omega)) -
          ∑ j : Fin M.memory, M.recurrenceCoeff j.castSucc •
            rec (n-M.memory+j) (by omega))

theorem run_initial (g : E → E) (initial : Fin M.memory → E) (j : Fin M.memory) :
    M.run g initial j = initial j := by
  rw [run, Nat.strongRec_eq]
  simp only [j.isLt, ↓reduceDIte]

theorem run_step (g : E → E) (initial : Fin M.memory → E) (k : ℕ) :
    M.run g initial (k+M.memory) =
      (M.recurrenceCoeff (Fin.last M.memory))⁻¹ •
        (g (M.query (M.run g initial) k) -
          ∑ j : Fin M.memory, M.recurrenceCoeff j.castSucc • M.run g initial (k+j)) := by
  conv_lhs => rw [run, Nat.strongRec_eq]
  simp only [show ¬k+M.memory<M.memory by omega, ↓reduceDIte,
    Nat.add_sub_cancel_right]
  rfl

theorem run_isTrajectory (g : E → E) (initial : Fin M.memory → E) :
    M.IsTrajectory g (M.run g initial) := by
  intro k
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  rw [M.run_step, smul_smul, mul_inv_cancel₀ M.leading_ne, one_smul]
  abel

theorem IsTrajectory.step {g : E → E} {w : ℕ → E} (h : M.IsTrajectory g w) (k : ℕ) :
    w (k+M.memory) =
      (M.recurrenceCoeff (Fin.last M.memory))⁻¹ •
        (g (M.query w k) -
          ∑ j : Fin M.memory, M.recurrenceCoeff j.castSucc • w (k+j)) := by
  have hh := h k
  rw [Fin.sum_univ_castSucc] at hh
  simp only [Fin.val_castSucc, Fin.val_last] at hh
  rw [← hh]
  simp only [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ M.leading_ne, one_smul]

theorem IsTrajectory.unique {g : E → E} {w z : ℕ → E}
    (hw : M.IsTrajectory g w) (hz : M.IsTrajectory g z)
    (hinitial : ∀ j : Fin M.memory, w j = z j) : w = z := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n<M.memory
    · exact hinitial ⟨n,hn⟩
    · have he : n=(n-M.memory)+M.memory := by omega
      rw [he, hw.step, hz.step]
      congr 2
      · congr 1
        apply Finset.sum_congr rfl
        intro j _
        rw [ih (n-M.memory+j) (by omega)]
      · apply Finset.sum_congr rfl
        intro j _
        rw [ih (n-M.memory+j) (by omega)]

theorem IsTrajectory.eq_run {g : E → E} {w : ℕ → E} (h : M.IsTrajectory g w) :
    w = M.run g (fun j => w j) :=
  IsTrajectory.unique M h (M.run_isTrajectory g _) (fun j => (M.run_initial g (fun i => w i) j).symm)

end
end nesterov.StationaryMethod
