import krylov.Functions.NativeRFCFNormalizedRestarted
import krylov.Functions.CubicRestartDecay

/-!
Article: main_krylov, prop:Fcycle(ii), cubic R-order of the real restarts.
Use: apply the elementary R-order conversion to the actual normalized-reference
RFC-F recursion. The conclusion is an explicit doubly exponential bound on
the real restart errors, including exact stationary tails.
Source: the proved native cubic estimate and elementary error induction.
-/
namespace krylov.Functions
noncomputable section
open Set Filter Topology Metric krylov.Methods krylov.Reference krylov.Nonlinear
  chebyshev1.Nonlinear
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k : ℕ}

/-- The real restarted RFC-F sequence has cubic R-order under the literal
observed-reference assumption s7:N. No frozen direction compactness or rate
assumption is used. Article: main_krylov, prop:Fcycle(ii). -/
theorem restarted_nativeRFCF_normalized_decay
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef) (hk : 0<k)
    (T : EuclideanSpace ℝ (Fin (k+1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : EuclideanSpace ℝ (Fin (k+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)))
    (H : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (D₃ : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hD₃ : HasFDerivAt H D₃ 0)
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
    let x := rfcFRestartedPoints T f G r k x₀
    let e := fun c=>‖T (x c)‖
    (∀ᶠ c in atTop, 0<e c →
      normalizedReference (rfcFunctionSearchOperator T f G H fullMemory r (x c) 0) (G (x c))∈K) →
    Tendsto e atTop (𝓝 0) →
    ∃ N : ℕ, ∃ M : ℝ, 0<M ∧ ∀ j : ℕ, e (N+j)≤M*(1/2:ℝ)^(3^j)  := by
  dsimp only
  intro hN hconv
  have hrec := restarted_nativeRFCF_normalized_cubic base hb hk T hT f G H D₃ hD₃
    hr hG₀ hH₀ hHc₀ hLr hH hF hG K hK hquad x₀ hN hconv
  exact cubic_restart_decay _ (fun c=>norm_nonneg _) hconv hrec

end
end krylov.Functions
