import krylov.Envelope.FinalizedTilt
import krylov.Envelope.SelectionMinimax
import krylov.Methods.FinalizedCorrectionCount

set_option autoImplicit false
/-!
Article: Theorem B.16 [thm:select] of krylov.tex.
Use: prove every actual smooth source method becomes a genuine minimax
attainer after one real final latest-model correction; correction-free
original methods produce true at-most-one-correction subclass attainers.
Source: constructed genuine primitive smooth final wrapper, its actual
minus-tilt response and the real attained RFC selection maximum.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability Matrix Set
open scoped Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- The genuine final latest-information wrapper of every actual smooth source method attains the true common-tilt maximum on the real full scenario budget.
Use: The genuine final latest-information wrapper of every actual smooth source method attains the true common-tilt maximum on the real full scenario budget.
Article: main_krylov, thm:select and s3:cor:qn, genuine final-correction minimax attainers.
Proof: Its actual scenario response equals the genuine RFC response on every real scenario, including all independent correction defects. -/
theorem finalized_selection_value_attained (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g)
    (ω : Fin (N-1) → ℝ≥0) :
    IsGreatest ((fun Θ => ‖scenarioVariation (finalizedMethod M.policy N) base g N Θ‖) '' scenarioBudget N ω)
      (selectionValue base g N ω) := by
  -- The complete genuine scenario response agrees with actual RFC, so its real maximizing scenario remains an attainer.
  have he : (fun Θ => ‖scenarioVariation (finalizedMethod M.policy N) base g N Θ‖)=
      (fun Θ => ‖scenarioVariation (rfcMethod fullMemory 1) base g N Θ‖) := by
    funext Θ
    rw [finalized_scenario_variation M base hb g N hcount,
      rfc_scenario_variation 1 (by norm_num) base hb g N hN hcount]
  rw [he]
  exact rfc_selection_value_attained base hb g N hN hcount ω

/-- The true worst transverse variation of every genuine finalized smooth source method equals exactly the actual selection value.
Use: The true worst transverse variation of every genuine finalized smooth source method equals exactly the actual selection value.
Article: main_krylov, thm:select and s3:cor:qn, genuine final-correction minimax attainers.
Proof: Take the real supremum of the proved attained genuine scenario maximum. -/
theorem finalized_worstTransverse_eq_selectionValue (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g)
    (ω : Fin (N-1) → ℝ≥0) :
    worstTransverse (finalizedSmoothClass M N).policy base g N ω=selectionValue base g N ω :=
  (finalized_selection_value_attained M base hb g N hN hcount ω).csSup_eq

/-- The actual final wrapper of any genuine smooth method has worst transverse variation at most that of every true smooth source-class competitor.
Use: The actual final wrapper of any genuine smooth method has worst transverse variation at most that of every true smooth source-class competitor.
Article: main_krylov, thm:select and s3:cor:qn, genuine final-correction minimax attainers.
Proof: Combine its real attained selection equality with the genuine absorbed-information lower bound for the actual competing method. -/
theorem finalized_transverse_optimal (M L : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g)
    (ω : Fin (N-1) → ℝ≥0) :
    worstTransverse (finalizedSmoothClass M N).policy base g N ω≤worstTransverse L.policy base g N ω := by
  rw [finalized_worstTransverse_eq_selectionValue M base hb g N hN hcount ω]
  exact selection_le_worstTransverse L base hb g N hN hcount ω

/-- The actual primitive smooth final wrapper of every genuine correction-free source method belongs to the true at-most-one-correction subclass.
Use: The actual primitive smooth final wrapper of every genuine correction-free source method belongs to the true at-most-one-correction subclass.
Article: main_krylov, thm:select and s3:cor:qn, genuine final-correction minimax attainers.
Proof: Use its real one-query correction-tree bound on every possible actual observed branch. -/
theorem finalized_correctionFree_oneCorrection (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (hm : CorrectionFree M.policy) (N : ℕ) : OneCorrectionMethod (finalizedSmoothClass M N).policy :=
  finalizedMethod_oneCorrection M.policy hm N
end
end krylov.Envelope
