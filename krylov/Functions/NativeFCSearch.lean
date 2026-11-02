import krylov.Functions.SearchMidpointTransfer
import krylov.Methods.FC

/-!
Article: main_krylov, alg:fc, lem:cycle-transfer and thm:Htransfer.
Use: instantiate the actual adaptive search executor with FC's genuine
observed step/secant dictionary and its existing retained-window solve.
Derive true query localization before substituting averaged Hessians.
Source: Algorithm FC, the reused data-only windowDirection, and Appendix G.
-/

namespace krylov.Functions
noncomputable section
open Set Metric krylov.Methods chebyshev1.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual observed step/secant pairs from a newest-first list of physical query points.
Article: main_krylov, alg:fc, append the true step and gradient difference. -/
def fcFunctionPairs (G : E → E) : List E → List (E × E)
  | [] => []
  | [_] => []
  | x :: y :: rest => (x - y, G x - G y) :: fcFunctionPairs G (y :: rest)

/-- The real FC direction reuses the existing observed retained-window solver.
Article: main_krylov, alg:fc, with arbitrary full, restarted or sliding memory. -/
def fcFunctionDirection (G : E → E) (memory : ℕ → ℕ) (x₀ : E) (hist : List E) : E :=
  windowDirection ((fcFunctionPairs G hist).take (memory (hist.length - 1))) (G (hist.headD x₀))

/-- The actual physical FC query sequence uses objective minimization on each real search chord.
Article: main_krylov, alg:fc, the search-only branch.
Use: every direction and retained pair is computed from actual observed points and gradients. -/
def fcFunctionPoint (f : E → ℝ) (G : E → E) (memory : ℕ → ℕ)
    (r : ℝ) (x₀ : E) : ℕ → E := exactSearchPoint f r (fcFunctionDirection G memory x₀) x₀

/-- The genuine actual FC observed history is the adaptive search history of physical query points.
Article: main_krylov, alg:fc, no prescribed trajectory or assumed remainder. -/
def fcFunctionHistory (f : E → ℝ) (G : E → E) (memory : ℕ → ℕ)
    (r : ℝ) (x₀ : E) : ℕ → List E := exactSearchHistory f r (fcFunctionDirection G memory x₀) x₀

/-- Every native FC function step is the actual unique local exact search for its computed direction.
Article: main_krylov, alg:fc and apG:E.
Proof: instantiate the proved adaptive executor with the real FC window solve. -/
theorem fcFunctionPoint_chord_steps (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) {r : ℝ} (hr : 0 < r)
    (hH₀ : H 0 = ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L H (closedBall 0 r))
    (hF : ∀ z ∈ closedBall (0 : E) r, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z ∈ closedBall (0 : E) r, HasFDerivAt G (H z) z)
    (memory : ℕ → ℕ) (x₀ : E) (hx₀ : x₀ ∈ closedBall (0 : E) r) :
    ∀ k : ℕ, IsChordMinimum f (fcFunctionPoint f G memory r x₀ k)
      (fcFunctionDirection G memory x₀ (fcFunctionHistory f G memory r x₀ k)) r
      (fcFunctionPoint f G memory r x₀ (k + 1)) :=
  exactSearchPoint_chord_steps f G H hr hH₀ hLr hH hF hG (fcFunctionDirection G memory x₀) x₀ hx₀

variable [CompleteSpace E]

/-- Native FC query localization is derived from the real objective and its derivatives.
Article: main_krylov, lem:cycle-transfer, actual FC O(e_c) query bound.
Proof: the true data-only FC solve is an admitted adaptive history rule; all
its real searches stay in the initial objective sublevel set. -/
theorem fcFunctionPoint_localization (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) {r : ℝ} (hr : 0 < r)
    (hG₀ : G 0 = 0) (hH₀ : H 0 = ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L H (closedBall 0 r))
    (hF : ∀ z ∈ closedBall (0 : E) r, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z ∈ closedBall (0 : E) r, HasFDerivAt G (H z) z)
    (memory : ℕ → ℕ) (x₀ : E) (hx₀ : ‖x₀‖ < r / 2) :
    ∀ k : ℕ, ‖fcFunctionPoint f G memory r x₀ k‖ ≤ Real.sqrt 3 * ‖x₀‖ ∧
      ‖fcFunctionPoint f G memory r x₀ k‖ ≤ (1 + 2 * (L : ℝ) * ‖x₀‖) * ‖x₀‖ ∧
      fcFunctionPoint f G memory r x₀ k ∈ ball (0 : E) r :=
  exactSearchPoint_localization f G H hr hG₀ hH₀ hLr hH hF hG (fcFunctionDirection G memory x₀) x₀ hx₀

/-- The native FC segment operators have genuine third-derivative midpoint increments.
Article: main_krylov, thm:Htransfer, the actual-midpoint part of FC transfer.
Proof: reuse the real adaptive-search midpoint theorem after deriving all of
the native FC query bounds. Quadratic-reference replacement remains separate. -/
theorem fcFunctionPoint_hessian_increment (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) (T : E →L[ℝ] E →L[ℝ] E)
    {r : ℝ} (hr : 0 < r) (hG₀ : G 0 = 0) (hH₀ : H 0 = ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L H (closedBall 0 r))
    (hF : ∀ z ∈ closedBall (0 : E) r, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z ∈ closedBall (0 : E) r, HasFDerivAt G (H z) z)
    (hD : HasFDerivAt H T 0) :
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ x₀ : E, ‖x₀‖ < δ → ∀ memory : ℕ → ℕ, ∀ k : ℕ,
      let x := fcFunctionPoint f G memory r x₀
      let s := fun j => x (j + 1) - x j
      let m := fun j => x j + (1 / 2 : ℝ) • s j
      ‖averagedDerivative H (x (k + 1)) (s (k + 1)) - averagedDerivative H (x k) (s k) -
        T (m (k + 1) - m k)‖ ≤ η * ‖x₀‖ := by
  intro η hη
  obtain ⟨δ, hδ, hinc⟩ := exactSearchPoint_hessian_increment f G H T hr hG₀ hH₀ hLr hH hF hG hD η hη
  exact ⟨δ, hδ, fun x₀ hx₀ memory => hinc x₀ hx₀ (fcFunctionDirection G memory x₀)⟩

end
end krylov.Functions
