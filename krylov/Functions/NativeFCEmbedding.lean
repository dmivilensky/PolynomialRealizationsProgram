import krylov.Functions.NativeFCOperators

/-!
Article: main_krylov, lem:cycle-transfer and thm:Htransfer, faithful native FC embedding.
Use: identify the complete actual function execution with the repository's
existing operator policy execution on its true segment averages. Every query
bound and every exact-search quotient is derived from the original function.
Source: Algorithm FC and the proved genuine local-search/operator dictionary.
-/

namespace krylov.Functions
noncomputable section
open Set Metric krylov.Methods chebyshev1.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The complete genuine nonlinear FC history equals the existing FC operator execution on its actual averages.
Article: main_krylov, lem:cycle-transfer, faithful native function/operator execution.
Proof: actual objective sublevels first localize every query. The genuine FTC
and stationarity identify each actual search with the existing quotient. The
true measured pair dictionary identifies the existing FC direction at every step. -/
theorem fcFunctionObservedHistory_eq_fcHistory (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) {r : ℝ} (hr : 0 < r)
    (hG₀ : G 0 = 0) (hH₀ : H 0 = ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L H (closedBall 0 r))
    (hF : ∀ z ∈ closedBall (0 : E) r, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z ∈ closedBall (0 : E) r, HasFDerivAt G (H z) z)
    (memory : ℕ → ℕ) (x₀ : E) (hx₀ : ‖x₀‖ < r / 4) :
    ∀ k : ℕ, fcFunctionObservedHistory f G H memory r x₀ k =
      fcHistory memory (fcFunctionOperator f G H memory r x₀) (G x₀) k := by
  have hx : ‖x₀‖ < r / 2 := by linarith
  have hx' : x₀ ∈ closedBall (0 : E) r := by
    rw [mem_closedBall, dist_zero_right]
    linarith [norm_nonneg x₀]
  have hloc := fcFunctionPoint_localization f G H hr hG₀ hH₀ hLr hH hF hG memory x₀ hx
  have hsteps := fcFunctionPoint_chord_steps f G H hr hH₀ hLr hH hF hG memory x₀ hx'
  have hsqrt : Real.sqrt (3 : ℝ) ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  have hinput k : ‖fcFunctionPoint f G memory r x₀ k‖ < r / 2 := by
    have hn := (hloc k).1.trans (mul_le_mul_of_nonneg_right hsqrt (norm_nonneg x₀))
    linarith
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    let prev := fcFunctionObservedHistory f G H memory r x₀ k
    let d := fcFunctionDirection G memory x₀ (fcFunctionHistory f G memory r x₀ k)
    let A := fcFunctionOperator f G H memory r x₀ k
    have hd : (fcMethod memory).direction prev = d :=
      fcFunctionObservedHistory_direction f G H memory r x₀ k
    have hg : prev.gradient = G (fcFunctionPoint f G memory r x₀ k) :=
      fcFunctionObservedHistory_gradient f G H memory r x₀ k
    have hbridge := local_chord_operator_search f G H hr hG₀ hH₀ hLr hH hF hG
      (fcFunctionPoint f G memory r x₀ k) d (fcFunctionPoint f G memory r x₀ (k + 1))
      (hinput k) (hsteps k)
    change fcFunctionPoint f G memory r x₀ (k + 1) - fcFunctionPoint f G memory r x₀ k =
        krylov.Reference.lineLength (G (fcFunctionPoint f G memory r x₀ k)) d (A d) • d ∧
      G (fcFunctionPoint f G memory r x₀ (k + 1)) =
        krylov.Reference.searchedGradient (G (fcFunctionPoint f G memory r x₀ k)) d (A d) at hbridge
    change fcFunctionObservedHistory f G H memory r x₀ (k + 1) =
      methodAdvance (fcMethod memory) A A
        (fcHistory memory (fcFunctionOperator f G H memory r x₀) (G x₀) k)
    rw [← ih]
    change ⟨G x₀, ⟨d, A d,
      fcFunctionPoint f G memory r x₀ (k + 1) - fcFunctionPoint f G memory r x₀ k,
      G (fcFunctionPoint f G memory r x₀ (k + 1)), []⟩ :: prev.records⟩ =
        methodAdvance (fcMethod memory) A A prev
    rw [methodAdvance, hd, hg]
    simp only [fcMethod, retainedMethod, runCorrections, add_zero]
    rw [← hbridge.1, ← hbridge.2]
    have hi : prev.initial = G x₀ := fcFunctionObservedHistory_initial f G H memory r x₀ k
    rw [hi]

/-- The actual function gradient equals the actual operator FC gradient, with no surrogate transcript.
Article: main_krylov, lem:cycle-transfer, exact response substitution. -/
theorem fcFunction_gradient_eq_fcGradient (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) {r : ℝ} (hr : 0 < r)
    (hG₀ : G 0 = 0) (hH₀ : H 0 = ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L H (closedBall 0 r))
    (hF : ∀ z ∈ closedBall (0 : E) r, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z ∈ closedBall (0 : E) r, HasFDerivAt G (H z) z)
    (memory : ℕ → ℕ) (x₀ : E) (hx₀ : ‖x₀‖ < r / 4) (k : ℕ) :
    G (fcFunctionPoint f G memory r x₀ k) =
      fcGradient memory (fcFunctionOperator f G H memory r x₀) (G x₀) k := by
  rw [fcGradient, ← fcFunctionObservedHistory_eq_fcHistory f G H hr hG₀ hH₀ hLr hH hF hG memory x₀ hx₀ k,
    fcFunctionObservedHistory_gradient]

end
end krylov.Functions
