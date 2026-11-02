import krylov.Convergence.VirtualDirectionTensorLeading
import krylov.Convergence.OneGradientC3Source

/-!
Article: main_krylov, thm:V, original C-three hypotheses.
Use: obtain the genuine printed native tensor expansion from a continuous
actual third derivative, deriving the local Hessian Lipschitz constant.
Source: true derivative mean-value calculus and native compact transfer.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Functions krylov.Nonlinear
  krylov.Stability krylov.OneGradient krylov.Secant
open scoped InnerProductSpace NNReal
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The true printed tensor leading term under original C-three source
regularity; no Hessian Lipschitz constant is an additional premise. -/
theorem xrfcDFunction_C3_tensor_leading_gradient
    (trial : History E → ℝ) (hhom : ObservedTrialHomogeneous trial)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (U : Set E) (hU : IsCompact U)
    (hcount : ∀ u∈U,referenceAtomCount base hb (cgOperator base u)=n)
    (ht : ∀ u∈U,∀ i<n,0<trial (oneGradientRun (xrfcDMethod fullMemory trial)
      (fun _=>cgOperator base) (cgOperator base u) i))
    (hT : ∀ u∈U,∀ i<n,ContDiffAt ℝ 2 (trialCoordinate trial i)
      (oneGradientData (xrfcDMethod fullMemory trial) (fun _=>cgOperator base) (cgOperator base u) i))
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (r : ℝ) (hr : 0<r)
    (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base)
    (hF : ∀ x∈ball 0 r,HasFDerivAt f (innerSL ℝ (G x)) x)
    (hG : ∀ x∈ball 0 r,HasFDerivAt G (H x) x)
    (D : E → E →L[ℝ] E →L[ℝ] E)
    (hD : ∀ z∈ball 0 r,HasFDerivAt H (D z) z) (hDc : ContinuousAt D 0) (hn : 0<n) :
    ∀ η : ℝ,0<η →∃ ep : ℝ,0<ep ∧∀ ε : ℝ,0<ε →ε<ep →∀ u∈U,
      ‖cgOperator (metricRoot base)⁻¹ (G (xrfcDFunctionOutput trial G (ε • u)))-
        ε^2 • xrfcDTensorCoefficient trial base (D 0) u‖≤η*ε^2 := by
  obtain ⟨s,L,hs,hsr,hLip⟩ := exists_hessian_lipschitz_ball H D hr hD hDc
  have hsub : ball (0:E) s⊆ball 0 r := ball_subset_ball hsr
  exact xrfcDFunction_compact_tensor_leading_gradient trial hhom base hb U hU hcount ht hT
    f G H s hs hG₀ hH₀ hLip (fun z hz=>hF z (hsub hz)) (fun z hz=>hG z (hsub hz))
    (D 0) (hD 0 (mem_ball_self hr)) hn

end
end krylov.Convergence
