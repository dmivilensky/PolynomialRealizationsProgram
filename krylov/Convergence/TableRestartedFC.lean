import krylov.Convergence.RestartedFCOrder
import krylov.Convergence.OrderCounting

/-!
Article: main_krylov, Table s7-orders, actual restarted FC iteration clock.
Use: prove the literal order of every real intermediate FC iterate, not only
of a repeated cycle-end envelope. The true objective localization supplies
the actual intermediate-iterate comparison; its finite initial exceptions
are absorbed by the global R-order theorem.
Source: native scalar FC localization and exact integral cost conversion.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Nonlinear krylov.Functions
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k : ℕ}

/-- All genuine iterates of fresh full-memory FC cycles, in the original
single-iteration clock. Article: main_krylov, Table s7-orders. -/
def fcRestartedIterate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (r : ℝ) (N : ℕ) (x₀ : E) (j : ℕ) : E :=
  metricFCPoint T f G fullMemory r (fcRestartedPoints T f G r N x₀ (j/N)) (j%N)

/-- Actual restarted FC has the printed order 2^(1/n) at every actual
iteration, hence at every counted gradient under the source convention.
The intermediate point bound is derived, not assumed.
Article: main_krylov, thm:D and Table s7-orders. -/
theorem restarted_nativeFC_iteration_rorder
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (T : EuclideanSpace ℝ (Fin (k+1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : EuclideanSpace ℝ (Fin (k+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)))
    (H : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base)
    (hHc₀ : coordinateDerivative T H 0=ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (k+1))))
    {L : ℝ≥0} (hLr : (L : ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z, ‖T z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z, ‖T z‖≤r → HasFDerivAt G (H z) z)
    (K : Set ((EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1))) ×
      EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hquad : ∀ z∈K, z.1.toLinearMap.IsSymmetric ∧
      (∀ v, v≠0 → 0 < inner ℝ v (z.1 v)) ∧ ∀ i<k+1, CG.gradient z.1 z.2 i≠0)
    (x₀ : EuclideanSpace ℝ (Fin (k+1))) :
    let x := fcRestartedPoints T f G r (k+1) x₀
    let e := fun c=>‖T (x c)‖
    (∀ᶠ c in atTop, 0<e c →
      normalizedReference (metricFCOperator T f G H fullMemory r (x c) 0) (G (x c))∈K) →
    Tendsto e atTop (𝓝 0) →
    HasROrder (fun j=>‖T (fcRestartedIterate T f G r (k+1) x₀ j)‖) ((2:ℝ)^(1/((k+1:ℕ):ℝ))) := by
  dsimp only
  intro hN hconv
  let x := fcRestartedPoints T f G r (k+1) x₀
  let e := fun c=>‖T (x c)‖
  have hcycle := restarted_nativeFC_normalized_rorder base hb T hT f G H
    hr hG₀ hH₀ hHc₀ hLr hH hF hG K hK hquad x₀ hN hconv
  have hcost : 0<k+1 := by omega
  have hclock := hcycle.clock (by norm_num : (1:ℝ)<2) (k+1) hcost
  apply hclock.eventually_mono (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<3))
  obtain ⟨N,hsmall⟩ := eventually_atTop.mp (hconv.eventually (gt_mem_nhds (half_pos hr)))
  filter_upwards [eventually_ge_atTop (N*(k+1))] with j hj
  have hidx : N≤j/(k+1) := (Nat.le_div_iff_mul_le hcost).mpr hj
  exact (metricFCPoint_localization T hT f G H hr hG₀ hHc₀ hLr hH hF hG
    fullMemory (x (j/(k+1))) (hsmall _ hidx) (j%(k+1))).1

end
end krylov.Convergence
