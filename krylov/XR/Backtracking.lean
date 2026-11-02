import krylov.XR.BacktrackingDescent
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Article: main_krylov, alg:xr and thm:XR, literal fixed-direction backtracking.
Use: execute the actual clipped quotient update, prove that it terminates,
and recover the printed uniform lower bound on the accepted step.
Source: the genuine descent lemma, geometric decay, and the first accepted
index. The algorithm itself does not take an acceptance certificate as input.
-/

namespace krylov.XR
noncomputable section
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual quotient clipping in the rejected-trial update. -/
def reductionFactor (chi : ℝ) : ℝ := min (max chi 2) 10

/-- The sequence of trials which would be tested if execution continued.
Only its prefix through the first accepted index is actually evaluated. -/
def backtrackingSteps (f : E → ℝ) (x g u : E) : ℕ → ℝ
  | 0 => 1
  | j + 1 => backtrackingSteps f x g u j /
      reductionFactor (trialQuotient f x g u (backtrackingSteps f x g u j))

/-- First accepted trial, with a total default outside the mathematical
domain where termination will be proved. -/
def backtrackingIndex (f : E → ℝ) (sigma : ℝ) (x g u : E) : ℕ := by
  classical
  exact if h : ∃ j, Accepted f sigma x g u (backtrackingSteps f x g u j)
    then Nat.find h else 0

/-- The actual accepted step length, obtained by executing the quotient
updates, rather than chosen arbitrarily from the acceptable interval. -/
def backtrackingLength (f : E → ℝ) (sigma : ℝ) (x g u : E) : ℝ :=
  backtrackingSteps f x g u (backtrackingIndex f sigma x g u)

/-- All clipping factors lie in the printed interval [2,10]. -/
theorem reductionFactor_bounds (chi : ℝ) :
    2 ≤ reductionFactor chi ∧ reductionFactor chi ≤ 10 := by
  exact ⟨le_min (le_max_right _ _) (by norm_num), min_le_right _ _⟩

/-- All generated trials are positive, with the geometric upper bound
needed to prove finite termination. -/
theorem backtrackingSteps_bounds (f : E → ℝ) (x g u : E) (j : ℕ) :
    0 < backtrackingSteps f x g u j ∧
      backtrackingSteps f x g u j ≤ (1 / 2 : ℝ) ^ j := by
  induction j with
  | zero => simp [backtrackingSteps]
  | succ j ih =>
    have hc := reductionFactor_bounds
      (trialQuotient f x g u (backtrackingSteps f x g u j))
    have hcpos : 0 < reductionFactor
        (trialQuotient f x g u (backtrackingSteps f x g u j)) := by linarith
    constructor
    · exact div_pos ih.1 hcpos
    · change backtrackingSteps f x g u j / reductionFactor
          (trialQuotient f x g u (backtrackingSteps f x g u j)) ≤ _
      calc
        _ ≤ backtrackingSteps f x g u j / 2 :=
          div_le_div_of_nonneg_left ih.1.le (by norm_num) hc.1
        _ ≤ (1 / 2 : ℝ) ^ j / 2 := div_le_div_of_nonneg_right ih.2 (by norm_num)
        _ = _ := by rw [pow_succ]; ring

/-- Termination of the actual backtracking on every nonzero gradient,
derived from the genuine Lipschitz-gradient hypothesis and safeguard bounds. -/
theorem backtracking_terminates (f : E → ℝ) (G : E → E)
    (hF : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x)
    (L : ℝ≥0) (hL : 0 < (L : ℝ)) (hG : LipschitzWith L G)
    (c₁ c₂ sigma : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hsigma : sigma < 1) (x u : E) (hg : G x ≠ 0)
    (hu : GradientRelated c₁ c₂ (G x) u) :
    ∃ j, Accepted f sigma x (G x) u (backtrackingSteps f x (G x) u j) := by
  have he : 0 < 2 * (1 - sigma) * c₁ / ((L : ℝ) * c₂ ^ 2) := by positivity
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one he (by norm_num : (1 / 2 : ℝ) < 1)
  have hb := backtrackingSteps_bounds f x (G x) u j
  exact ⟨j, accepted_of_step_le f G hF L hL hG c₁ c₂ sigma hc₁ hc₂
    hsigma x u hg hu _ hb.1 (hb.2.trans hj.le)⟩

/-- The first-index implementation actually returns an accepted trial. -/
theorem backtrackingIndex_spec (f : E → ℝ) (sigma : ℝ) (x g u : E)
    (h : ∃ j, Accepted f sigma x g u (backtrackingSteps f x g u j)) :
    Accepted f sigma x g u (backtrackingLength f sigma x g u) ∧
      ∀ j < backtrackingIndex f sigma x g u,
        ¬ Accepted f sigma x g u (backtrackingSteps f x g u j) := by
  classical
  simp only [backtrackingLength, backtrackingIndex, dite_eq_left h]
  exact ⟨Nat.find_spec h, fun j hj => Nat.find_min h hj⟩

/-- The accepted real step has the exact lower bound printed in Theorem XR.
The factor five is the factor ten clipping combined with the factor two in
the genuine sufficient-acceptance threshold. -/
theorem backtrackingLength_lower (f : E → ℝ) (G : E → E)
    (hF : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x)
    (L : ℝ≥0) (hL : 0 < (L : ℝ)) (hG : LipschitzWith L G)
    (c₁ c₂ sigma : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hsigma : sigma < 1) (x u : E) (hg : G x ≠ 0)
    (hu : GradientRelated c₁ c₂ (G x) u) :
    min 1 ((1 - sigma) * c₁ / (5 * (L : ℝ) * c₂ ^ 2)) ≤
      backtrackingLength f sigma x (G x) u := by
  have hex := backtracking_terminates f G hF L hL hG c₁ c₂ sigma hc₁ hc₂
    hsigma x u hg hu
  have hs := (backtrackingIndex_spec f sigma x (G x) u hex).2
  generalize hn : backtrackingIndex f sigma x (G x) u = N
  cases N with
  | zero => simp [backtrackingLength, hn, backtrackingSteps]
  | succ j =>
    have hreject := hs j (by omega)
    have hb := backtrackingSteps_bounds f x (G x) u j
    have ht : 2 * (1 - sigma) * c₁ / ((L : ℝ) * c₂ ^ 2) <
        backtrackingSteps f x (G x) u j := by
      by_contra h
      exact hreject (accepted_of_step_le f G hF L hL hG c₁ c₂ sigma hc₁ hc₂
        hsigma x u hg hu _ hb.1 (le_of_not_gt h))
    have hc := reductionFactor_bounds
      (trialQuotient f x (G x) u (backtrackingSteps f x (G x) u j))
    have hfac : 0 < reductionFactor
      (trialQuotient f x (G x) u (backtrackingSteps f x (G x) u j)) := by linarith
    have hnext : backtrackingSteps f x (G x) u j / 10 ≤
        backtrackingLength f sigma x (G x) u := by
      rw [backtrackingLength, hn, backtrackingSteps]
      exact div_le_div_of_nonneg_left hb.1.le hfac hc.2
    apply (min_le_right _ _).trans
    apply le_trans _ hnext
    calc
      (1 - sigma) * c₁ / (5 * (L : ℝ) * c₂ ^ 2) =
          (2 * (1 - sigma) * c₁ / ((L : ℝ) * c₂ ^ 2)) / 10 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right ht.le (by norm_num)

end
end krylov.XR
