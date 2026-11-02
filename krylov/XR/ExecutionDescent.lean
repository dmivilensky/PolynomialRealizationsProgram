import krylov.XR.Execution

/-!
Article: main_krylov, thm:XR, descent of the actual one-probe executor.
Use: carry the proved termination and step lower bound through the rejected
probe, true endpoint cache, stationary stopping, and outer recursive state.
Source: the literal execution definitions and the genuine descent lemma.
-/

namespace krylov.XR
noncomputable section
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Printed uniform lower bound on accepted trial lengths. -/
def minimumLength (sigma c₁ c₂ L : ℝ) : ℝ :=
  min 1 ((1 - sigma) * c₁ / (5 * L * c₂ ^ 2))

/-- Even outside the convergence domain every returned trial length is
positive; the default of the totalized search is its positive first trial. -/
theorem outerSearch_length_pos (model : State E → ModelResult E)
    (f : E → ℝ) (G : E → E) (sigma : ℝ) (S : State E) :
    0 < (outerSearch model f G sigma S).length := by
  classical
  unfold outerSearch
  dsimp only
  split
  · norm_num
  · exact (backtrackingSteps_bounds _ _ _ _ _).1

/-- The printed lower bound survives the one rejected-probe reset. -/
theorem outerSearch_length_lower (model : State E → ModelResult E)
    (f : E → ℝ) (G : E → E)
    (hF : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x)
    (L : ℝ≥0) (hL : 0 < (L : ℝ)) (hG : LipschitzWith L G)
    (sigma : ℝ) (hsigma : sigma < 1) (S : State E)
    (hc₁ : 0 < S.descentConstant) (hc₂ : S.descentConstant ≤ S.normConstant)
    (hcache : S.gradient = G S.point) (hg : S.gradient ≠ 0) :
    minimumLength sigma S.descentConstant S.normConstant L ≤
      (outerSearch model f G sigma S).length := by
  classical
  unfold outerSearch
  dsimp only
  split
  · exact min_le_left _ _
  · dsimp only
    let M₀ := model S
    let u₀ := M₀.safeDirection S
    let S₁ := { M₀.updateState S with
      pairs := appendPositive M₀.pairs (observedTrialPair f G S u₀) }
    let u₁ := (model S₁).safeDirection S₁
    change minimumLength sigma S.descentConstant S.normConstant L ≤
      backtrackingLength f sigma S.point S.gradient u₁
    have hu : GradientRelated S.descentConstant S.normConstant S.gradient u₁ :=
      safeguard_gradientRelated _ _ _ hc₁ hc₂ _ _
    rw [hcache] at hu hg ⊢
    exact backtrackingLength_lower f G hF L hL hG _ _ sigma hc₁
      (hc₁.trans_le hc₂) hsigma _ _ hg hu

/-- Both safeguard constants remain fixed throughout outer execution. -/
theorem outerAdvance_constants (P : Parameters) (dimension : ℕ)
    (model : State E → ModelResult E) (f : E → ℝ) (G : E → E) (S : State E) :
    (outerAdvance P dimension model f G S).descentConstant = S.descentConstant ∧
      (outerAdvance P dimension model f G S).normConstant = S.normConstant := by
  classical
  unfold outerAdvance
  split <;> exact ⟨rfl, rfl⟩

/-- Actual endpoint caching is preserved by the stopped or accepted update. -/
theorem outerAdvance_cache (P : Parameters) (dimension : ℕ)
    (model : State E → ModelResult E) (f : E → ℝ) (G : E → E) (S : State E)
    (hf : S.value = f S.point) (hg : S.gradient = G S.point) :
    (outerAdvance P dimension model f G S).value =
        f (outerAdvance P dimension model f G S).point ∧
      (outerAdvance P dimension model f G S).gradient =
        G (outerAdvance P dimension model f G S).point := by
  classical
  unfold outerAdvance
  split
  · exact ⟨hf, hg⟩
  · exact ⟨rfl, rfl⟩

/-- The actual outer step has the exact uniform sufficient decrease from
Theorem XR, including stationary states and a rejected first probe. -/
theorem outerAdvance_sufficient_decrease (P : Parameters) (dimension : ℕ)
    (model : State E → ModelResult E) (f : E → ℝ) (G : E → E)
    (hF : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x)
    (L : ℝ≥0) (hL : 0 < (L : ℝ)) (hG : LipschitzWith L G)
    (hsigma : 0 < P.armijo) (hsigma₁ : P.armijo < 1) (S : State E)
    (hc₁ : 0 < S.descentConstant) (hc₂ : S.descentConstant ≤ S.normConstant)
    (hf : S.value = f S.point) (hg : S.gradient = G S.point) :
    (outerAdvance P dimension model f G S).value ≤ S.value -
      P.armijo * minimumLength P.armijo S.descentConstant S.normConstant L *
        S.descentConstant * ‖S.gradient‖ ^ 2 := by
  classical
  by_cases hzero : S.gradient = 0
  · simp [outerAdvance, hzero]
  · let R := outerSearch model f G P.armijo S
    have hr := outerSearch_gradientRelated model f G P.armijo S hc₁ hc₂
    have ht := outerSearch_length_pos model f G P.armijo S
    have hl := outerSearch_length_lower model f G hF L hL hG P.armijo hsigma₁
      S hc₁ hc₂ hg hzero
    have ha := outerSearch_accepted model f G hF L hL hG P.armijo hsigma₁
      S hc₁ hc₂ hg hzero
    have hn : 0 < ‖S.gradient‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hzero)
    have hs : inner ℝ S.gradient R.direction < 0 := hr.1.trans_lt (by nlinarith)
    have harm := (accepted_iff_armijo f P.armijo S.point S.gradient R.direction
      R.length ht hs).1 ha
    rw [← hf] at harm
    simp only [outerAdvance, ite_eq_right hzero]
    change f (S.point + R.length • R.direction) ≤ _
    have hgrad := mul_le_mul_of_nonneg_left hr.1 (mul_nonneg hsigma.le ht.le)
    have hlength := mul_le_mul_of_nonneg_right hl
      (mul_nonneg (mul_nonneg hsigma.le hc₁.le) hn.le)
    nlinarith

end
end krylov.XR
