import krylov.Functions.MetricFCSearch
import krylov.Functions.ExactSearchOperator

/-!
Article: main_krylov, lem:cycle-transfer, physical search/operator coupling.
Use: identify exact searches of the original physical algorithm with its true
averaged-Hessian quotient for an arbitrary positive reference metric. Only
the scalar objective is normalized; the original direction is preserved.
Source: Appendix G, genuine coordinate FTC and the local exact-search proof.
-/

namespace krylov.Functions
noncomputable section
open Set Metric krylov.Nonlinear krylov.Reference chebyshev1.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Primal directions and inverse-metric dual vectors preserve their actual scalar pairing.
Article: main_krylov, lem:cycle-transfer, original physical search quotient. -/
theorem metric_primal_dual_pairing (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric) (d g : E) :
    inner ℝ (T d) (T.symm g) = inner ℝ d g := by
  have h := hT (T d) g
  change inner ℝ (T.symm (T d)) g = inner ℝ (T d) (T.symm g) at h
  simpa only [T.symm_apply_apply] using h.symm

/-- Every real metric-chord search executes the original physical averaged-Hessian quotient.
Article: main_krylov, lem:cycle-transfer, arbitrary positive physical reference.
Proof: derive genuine coordinate objective and derivative fields, transport
the actual Bochner segment average, and cancel the metric maps in the real
search numerator and denominator. No transformed FC rule is substituted. -/
theorem metric_chord_operator_search (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    {r : ℝ} (hr : 0 < r) (hG₀ : G 0 = 0)
    (hH₀ : coordinateDerivative T H 0 = ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt G (H z) z)
    (x d y : E) (hx : ‖T x‖ < r / 2)
    (hy : IsChordMinimum (coordinateObjective T f) (T x) (T d) r (T y)) :
    let A := averagedDerivative H x (y - x)
    y - x = lineLength (G x) d (A d) • d ∧ G y = searchedGradient (G x) d (A d) := by
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
  have hx' : T x ∈ closedBall (0 : E) r := by
    rw [mem_closedBall, dist_zero_right]
    linarith [norm_nonneg (T x)]
  have hseg t (ht : t ∈ Icc (0 : ℝ) 1) : x + t • (y - x) ∈ T ⁻¹' closedBall (0 : E) r := by
    change T (x + t • (y - x)) ∈ closedBall (0 : E) r
    rw [map_add, map_smul, map_sub]
    apply (convex_closedBall (0 : E) r).add_smul_mem hx' _ ht
    simpa only [add_sub_cancel] using hy.1
  have hphys := coordinateDerivative_lipschitz_pullback T H hH
  have hc := hphys.continuousOn.comp
    (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hseg
  let A := averagedDerivative H x (y - x)
  let Ac := averagedDerivative (coordinateDerivative T H) (T x) (T y - T x)
  have hAc : Ac (T d) = T.symm (A d) := by
    dsimp only [Ac, A]
    rw [← map_sub]
    simpa only [T.symm_apply_apply] using averagedDerivative_coordinate_apply T H x (y - x) (T d) hc
  have hlength : lineLength (coordinateGradient T G (T x)) (T d) (Ac (T d)) =
      lineLength (G x) d (A d) := by
    rw [lineLength, lineLength, hAc]
    simp only [coordinateGradient, T.symm_apply_apply,
      metric_primal_dual_pairing T hT]
  have hb := local_chord_operator_search (coordinateObjective T f) (coordinateGradient T G)
    (coordinateDerivative T H) hr hg₀ hH₀ hLr hH hFc hGc (T x) (T d) (T y) hx hy
  change T y - T x = lineLength (coordinateGradient T G (T x)) (T d) (Ac (T d)) • T d ∧
    coordinateGradient T G (T y) =
      searchedGradient (coordinateGradient T G (T x)) (T d) (Ac (T d)) at hb
  rw [hlength] at hb
  constructor
  · have he := congrArg T.symm hb.1
    simpa only [map_sub, map_smul, T.symm_apply_apply] using he
  · have hgrad := hb.2
    simp only [searchedGradient] at hgrad
    rw [hlength] at hgrad
    have he := congrArg T hgrad
    change G y = G x + lineLength (G x) d (A d) • A d
    simpa only [coordinateGradient, T.symm_apply_apply, T.apply_symm_apply,
      hAc, map_add, map_smul] using he

end
end krylov.Functions
