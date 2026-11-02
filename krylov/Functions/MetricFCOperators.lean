import krylov.Functions.MetricSearchOperator
import krylov.Functions.NativeFCOperators
import krylov.Functions.ObservedSearchHistory

/-!
Article: main_krylov, lem:cycle-transfer and thm:Htransfer, physical native FC coupling.
Use: preserve the original physical FC direction and complete observations
for arbitrary positive reference metrics, and identify the genuine function
execution with the existing operator executor on actual Hessian averages.
Source: Algorithm FC, exact metric search transport and the observed protocol.
-/

namespace krylov.Functions
noncomputable section
open Set Metric krylov.Methods krylov.Nonlinear chebyshev1.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The metric-native physical executor starts at precisely its prescribed physical point.
Article: main_krylov, alg:fc. -/
theorem metricFCPoint_zero (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (memory : ℕ → ℕ)
    (r : ℝ) (x₀ : E) : metricFCPoint T f G memory r x₀ 0 = x₀ := by
  simp [metricFCPoint, exactSearchPoint, exactSearchHistory]

/-- The metric-native actual observed pairs are exactly the real physical steps and gradient secants.
Article: main_krylov, alg:fc and lem:cycle-transfer. -/
theorem metricFCHistory_pairs (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (memory : ℕ → ℕ)
    (r : ℝ) (x₀ : E) (k : ℕ) :
    fcFunctionPairs G (metricFCHistory T f G memory r x₀ k) =
      executedPairs
        (fun j => metricFCPoint T f G memory r x₀ (j + 1) - metricFCPoint T f G memory r x₀ j)
        (fun j => G (metricFCPoint T f G memory r x₀ (j + 1)) - G (metricFCPoint T f G memory r x₀ j)) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hne : metricFCHistory T f G memory r x₀ k ≠ [] := by
      intro h
      have hl := metricFCHistory_length T f G memory r x₀ k
      rw [h] at hl
      simp at hl
    rw [metricFCHistory_succ, fcFunctionPairs_cons G _ x₀ _ hne,
      metricFCHistory_head, ih]
    rfl

/-- The actual physical FC direction, computed from its full real query history.
Article: main_krylov, alg:fc, unchanged physical algorithm. -/
def metricFCPhysicalDirection (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (memory : ℕ → ℕ)
    (r : ℝ) (x₀ : E) (k : ℕ) : E :=
  fcFunctionDirection G memory x₀ (metricFCHistory T f G memory r x₀ k)

/-- The true Hessian average on the actual physical FC step.
Article: main_krylov, lem:cycle-transfer. -/
def metricFCOperator (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (memory : ℕ → ℕ) (r : ℝ) (x₀ : E) (k : ℕ) : E →L[ℝ] E :=
  averagedDerivative H (metricFCPoint T f G memory r x₀ k)
    (metricFCPoint T f G memory r x₀ (k + 1) - metricFCPoint T f G memory r x₀ k)

/-- The complete genuine observed FC history in original physical coordinates.
Article: main_krylov, alg:fc and lem:cycle-transfer. -/
def metricFCObservedHistory (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (memory : ℕ → ℕ) (r : ℝ) (x₀ : E) : ℕ → History E :=
  observedSearchHistory G (metricFCOperator T f G H memory r x₀)
    (metricFCPoint T f G memory r x₀) (metricFCPhysicalDirection T f G memory r x₀)

/-- The existing physical FC implementation chooses exactly the genuine native function direction.
Article: main_krylov, alg:fc, complete direction dictionary under a general positive metric. -/
theorem metricFCObservedHistory_direction (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) (memory : ℕ → ℕ) (r : ℝ) (x₀ : E) (k : ℕ) :
    (fcMethod memory).direction (metricFCObservedHistory T f G H memory r x₀ k) =
      metricFCPhysicalDirection T f G memory r x₀ k := by
  simp only [fcMethod, retainedMethod, selectedWindow, metricFCObservedHistory,
    observedSearchHistory_length, observedSearchHistory_gradient, observedSearchHistory_pairs,
    ← metricFCHistory_pairs, metricFCPhysicalDirection, fcFunctionDirection,
    metricFCHistory_length, Nat.add_sub_cancel, metricFCHistory_head]

variable [CompleteSpace E]

/-- The complete real physical FC execution equals the existing operator execution on true Hessian averages.
Article: main_krylov, lem:cycle-transfer, faithful arbitrary-positive-reference FC embedding.
Proof: the real physical algorithm has derived metric query bounds. At every
real search the genuine coordinate FTC determines the original physical
quotient; the actual observation dictionary then identifies the whole policy history. -/
theorem metricFCObservedHistory_eq_fcHistory (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    {r : ℝ} (hr : 0 < r) (hG₀ : G 0 = 0)
    (hH₀ : coordinateDerivative T H 0 = ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt G (H z) z)
    (memory : ℕ → ℕ) (x₀ : E) (hx₀ : ‖T x₀‖ < r / 4) :
    ∀ k : ℕ, metricFCObservedHistory T f G H memory r x₀ k =
      fcHistory memory (metricFCOperator T f G H memory r x₀) (G x₀) k := by
  have hx : ‖T x₀‖ < r / 2 := by linarith
  have hx' : ‖T x₀‖ ≤ r := by linarith [norm_nonneg (T x₀)]
  have hloc := metricFCPoint_localization T hT f G H hr hG₀ hH₀ hLr hH hF hG memory x₀ hx
  have hsteps := metricFCPoint_chord_steps T hT f G H hr hH₀ hLr hH hF hG memory x₀ hx'
  have hsqrt : Real.sqrt (3 : ℝ) ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  have hinput k : ‖T (metricFCPoint T f G memory r x₀ k)‖ < r / 2 := by
    have hn := (hloc k).1.trans (mul_le_mul_of_nonneg_right hsqrt (norm_nonneg (T x₀)))
    linarith
  have hbridge k := metric_chord_operator_search T hT f G H hr hG₀ hH₀ hLr hH hF hG
    (metricFCPoint T f G memory r x₀ k) (metricFCPhysicalDirection T f G memory r x₀ k)
    (metricFCPoint T f G memory r x₀ (k + 1)) (hinput k)
    ((isChordMinimum_coordinate_iff T f _ _ _ r).mpr (hsteps k))
  have he := observedSearchHistory_eq_fcHistory G (metricFCOperator T f G H memory r x₀)
    (metricFCPoint T f G memory r x₀) (metricFCPhysicalDirection T f G memory r x₀) memory
    (metricFCObservedHistory_direction T f G H memory r x₀) (fun k => (hbridge k).1) (fun k => (hbridge k).2)
  simpa only [metricFCObservedHistory, metricFCPoint_zero] using he

/-- Every genuine physical FC displacement equals the existing operator executor's actual line step.
Article: main_krylov, lem:cycle-transfer, exact native step identification.
Proof: identify the complete true histories, then read their identical newest measured pair. -/
theorem metricFCPoint_step_eq_fcStep (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    {r : ℝ} (hr : 0 < r) (hG₀ : G 0 = 0)
    (hH₀ : coordinateDerivative T H 0 = ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt G (H z) z)
    (memory : ℕ → ℕ) (x₀ : E) (hx₀ : ‖T x₀‖ < r / 4) (k : ℕ) :
    metricFCPoint T f G memory r x₀ (k + 1) - metricFCPoint T f G memory r x₀ k =
      fcStep memory (metricFCOperator T f G H memory r x₀) (G x₀) k := by
  have he := congrArg History.pairs
    (metricFCObservedHistory_eq_fcHistory T hT f G H hr hG₀ hH₀ hLr hH hF hG memory x₀ hx₀ (k + 1))
  rw [metricFCObservedHistory, observedSearchHistory_pairs, fcHistory_pairs] at he
  exact congrArg Prod.fst (List.cons.inj he).1

end
end krylov.Functions
