import krylov.Functions.NativeFCSearch
import krylov.Functions.ObjectiveCoordinates
import krylov.Nonlinear.CoordinateLipschitz

/-!
Article: main_krylov, lem:cycle-transfer, physical FC under a positive quadratic metric.
Use: keep the actual physical FC direction and all observed gradients while
performing its genuine local search in the constructed metric ball. The
transported direction is a primal vector, not the canonical negative gradient.
Source: Algorithm FC and the proved actual scalar coordinate dictionary.
-/

namespace krylov.Functions
noncomputable section
open Set Metric krylov.Nonlinear chebyshev1.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Transport the genuine physical FC direction computed from its actual physical query history.
Article: main_krylov, lem:cycle-transfer, preservation of the original algorithm. -/
def metricFCDirection (T : E ≃L[ℝ] E) (G : E → E) (memory : ℕ → ℕ) (x₀ : E)
    (hist : List E) : E := T (fcFunctionDirection G memory x₀ (hist.map T.symm))

/-- The actual physical FC query sequence with exact searches on the genuine metric chords.
Article: main_krylov, alg:fc and lem:cycle-transfer.
Use: supports every positive physical quadratic Hessian through its constructed metric root. -/
def metricFCPoint (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (memory : ℕ → ℕ)
    (r : ℝ) (x₀ : E) (k : ℕ) : E :=
  T.symm (exactSearchPoint (coordinateObjective T f) r (metricFCDirection T G memory x₀) (T x₀) k)

/-- The actual physical query history of the unchanged FC direction rule.
Article: main_krylov, lem:cycle-transfer, true physical observed dictionary. -/
def metricFCHistory (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (memory : ℕ → ℕ)
    (r : ℝ) (x₀ : E) (k : ℕ) : List E :=
  (exactSearchHistory (coordinateObjective T f) r (metricFCDirection T G memory x₀) (T x₀) k).map T.symm

/-- The physical metric FC query clock contains exactly all actual points.
Article: main_krylov, alg:fc, correct retained-window clock. -/
theorem metricFCHistory_length (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (memory : ℕ → ℕ)
    (r : ℝ) (x₀ : E) (k : ℕ) : (metricFCHistory T f G memory r x₀ k).length = k + 1 := by
  simp only [metricFCHistory, List.length_map]
  induction k with
  | zero => rfl
  | succ k ih =>
    change (exactSearchHistory (coordinateObjective T f) r (metricFCDirection T G memory x₀) (T x₀) k).length + 1 = _
    rw [ih]

/-- The next actual physical query is prepended to the complete old physical history.
Article: main_krylov, alg:fc. -/
theorem metricFCHistory_succ (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (memory : ℕ → ℕ)
    (r : ℝ) (x₀ : E) (k : ℕ) :
    metricFCHistory T f G memory r x₀ (k + 1) =
      metricFCPoint T f G memory r x₀ (k + 1) :: metricFCHistory T f G memory r x₀ k := rfl

/-- The actual current point is exactly the head of the physical observed history.
Article: main_krylov, alg:fc. -/
theorem metricFCHistory_head (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (memory : ℕ → ℕ)
    (r : ℝ) (x₀ : E) (k : ℕ) :
    (metricFCHistory T f G memory r x₀ k).headD x₀ = metricFCPoint T f G memory r x₀ k := by
  cases k with
  | zero => simp [metricFCHistory, metricFCPoint, exactSearchHistory, exactSearchPoint]
  | succ k => rfl

/-- Every native physical FC step is the genuine exact minimizer on its true metric chord.
Article: main_krylov, lem:cycle-transfer and apG:E, arbitrary positive physical reference.
Proof: derive the real coordinate objective and gradient derivatives, execute
the actual adaptive search with its transported physical direction, and use
the exact scalar whole-chord coordinate dictionary. -/
theorem metricFCPoint_chord_steps (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    {r : ℝ} (hr : 0 < r) (hH₀ : coordinateDerivative T H 0 = ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt G (H z) z)
    (memory : ℕ → ℕ) (x₀ : E) (hx₀ : ‖T x₀‖ ≤ r) :
    ∀ k : ℕ,
      ‖T (metricFCPoint T f G memory r x₀ (k + 1))‖ ≤ r ∧
      (∃ t : ℝ, metricFCPoint T f G memory r x₀ (k + 1) = metricFCPoint T f G memory r x₀ k +
        t • fcFunctionDirection G memory x₀ (metricFCHistory T f G memory r x₀ k)) ∧
      ∀ t : ℝ, ‖T (metricFCPoint T f G memory r x₀ k +
        t • fcFunctionDirection G memory x₀ (metricFCHistory T f G memory r x₀ k))‖ ≤ r →
        f (metricFCPoint T f G memory r x₀ (k + 1)) ≤
          f (metricFCPoint T f G memory r x₀ k +
            t • fcFunctionDirection G memory x₀ (metricFCHistory T f G memory r x₀ k)) := by
  have hFc z (hz : z ∈ closedBall (0 : E) r) :
      HasFDerivAt (coordinateObjective T f) (innerSL ℝ (coordinateGradient T G z)) z := by
    apply coordinateObjective_hasFDerivAt T hT f G z
    apply hF
    simpa only [T.apply_symm_apply, mem_closedBall, dist_zero_right] using hz
  have hGc z (hz : z ∈ closedBall (0 : E) r) :
      HasFDerivAt (coordinateGradient T G) (coordinateDerivative T H z) z := by
    apply coordinateGradient_hasFDerivAt T G H z
    apply hG
    simpa only [T.apply_symm_apply, mem_closedBall, dist_zero_right] using hz
  have hs := exactSearchPoint_chord_steps (coordinateObjective T f) (coordinateGradient T G)
    (coordinateDerivative T H) hr hH₀ hLr hH hFc hGc (metricFCDirection T G memory x₀) (T x₀)
    (by simpa only [mem_closedBall, dist_zero_right] using hx₀)
  intro k
  apply (isChordMinimum_coordinate_iff T f _ _ _ r).mp
  simpa only [metricFCPoint, metricFCDirection, metricFCHistory, T.apply_symm_apply] using hs k

variable [CompleteSpace E]

/-- All native physical FC queries have the proved O(e_c) bound in the genuine reference metric.
Article: main_krylov, lem:cycle-transfer, arbitrary positive physical quadratic reference.
Proof: the original physical direction is preserved, while the actual metric
objective sublevel argument provides the common shrinking query enclosure. -/
theorem metricFCPoint_localization (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    {r : ℝ} (hr : 0 < r) (hG₀ : G 0 = 0)
    (hH₀ : coordinateDerivative T H 0 = ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt G (H z) z)
    (memory : ℕ → ℕ) (x₀ : E) (hx₀ : ‖T x₀‖ < r / 2) :
    ∀ k : ℕ, ‖T (metricFCPoint T f G memory r x₀ k)‖ ≤ Real.sqrt 3 * ‖T x₀‖ ∧
      ‖T (metricFCPoint T f G memory r x₀ k)‖ ≤ (1 + 2 * (L : ℝ) * ‖T x₀‖) * ‖T x₀‖ ∧
      ‖T (metricFCPoint T f G memory r x₀ k)‖ < r := by
  have hFc z (hz : z ∈ closedBall (0 : E) r) :
      HasFDerivAt (coordinateObjective T f) (innerSL ℝ (coordinateGradient T G z)) z := by
    apply coordinateObjective_hasFDerivAt T hT f G z
    apply hF
    simpa only [T.apply_symm_apply, mem_closedBall, dist_zero_right] using hz
  have hGc z (hz : z ∈ closedBall (0 : E) r) :
      HasFDerivAt (coordinateGradient T G) (coordinateDerivative T H z) z := by
    apply coordinateGradient_hasFDerivAt T G H z
    apply hG
    simpa only [T.apply_symm_apply, mem_closedBall, dist_zero_right] using hz
  have hg₀ : coordinateGradient T G 0 = 0 := by simp only [coordinateGradient, map_zero, hG₀]
  have hl := exactSearchPoint_localization (coordinateObjective T f) (coordinateGradient T G)
    (coordinateDerivative T H) hr hg₀ hH₀ hLr hH hFc hGc (metricFCDirection T G memory x₀) (T x₀) hx₀
  intro k
  simpa only [metricFCPoint, T.apply_symm_apply, mem_ball, dist_zero_right] using hl k

end
end krylov.Functions
