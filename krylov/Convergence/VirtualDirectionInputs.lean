import krylov.Convergence.VirtualDirectionLocalization
import krylov.Convergence.OneGradientSourceBounds

/-!
Article: main_krylov, thm:V, literal V1--V3 source construction.
Use: derive actual normalized initial-gradient and true evaluated/output
segment-operator perturbations and the complete scalar/operator dictionary.
Every native query bound is proved from primitive local function data and
the original compact direction family before the true source is assembled.
Source: true nonlinear localization and actual segment/radial FTC estimates.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Functions krylov.Nonlinear
  krylov.Stability
open scoped InnerProductSpace NNReal
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- All actual source inputs and exact query semantics follow from the
original trial and function assumptions. Article: main_krylov, thm:V. -/
theorem xrfcDFunction_compact_source_inputs
    (trial : History E → ℝ) (hhom : ObservedTrialHomogeneous trial)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (U : Set E) (hU : IsCompact U)
    (hcount : ∀ u∈U,referenceAtomCount base hb (cgOperator base u)=n)
    (ht : ∀ u∈U,∀ i<n,0<trial (oneGradientRun (xrfcDMethod fullMemory trial)
      (fun _=>cgOperator base) (cgOperator base u) i))
    (hT : ∀ u∈U,∀ i<n,ContDiffAt ℝ 2 (trialCoordinate trial i)
      (oneGradientData (xrfcDMethod fullMemory trial) (fun _=>cgOperator base) (cgOperator base u) i))
    (G : E → E) (H : E → E →L[ℝ] E) (r : ℝ) (hr : 0<r)
    (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base) {L : ℝ≥0} (hH : LipschitzOnWith L H (ball 0 r))
    (hG : ∀ x∈ball 0 r,HasFDerivAt G (H x) x) :
    ∃ ep C : ℝ,0<ep ∧0<C ∧∀ ε : ℝ,0<ε → ε<ep →∀ u∈U,
      ‖oneGradientFunctionInput (xrfcDMethod fullMemory trial) G H (cgOperator base) ε u n‖≤C*ε ∧
      oneGradientFunctionRun (xrfcDMethod fullMemory trial) G (ε • u) n=
        oneGradientRun (xrfcDMethod fullMemory trial)
          (oneGradientFunctionOperator (xrfcDMethod fullMemory trial) G H (ε • u)) (G (ε • u)) n ∧
      G (xrfcDFunctionOutput trial G (ε • u))=
        (xrfcDMethod fullMemory trial).outputGradient
          (oneGradientFunctionOutputOperator (xrfcDMethod fullMemory trial) G H (ε • u) n)
          (oneGradientRun (xrfcDMethod fullMemory trial)
            (oneGradientFunctionOperator (xrfcDMethod fullMemory trial) G H (ε • u)) (G (ε • u)) n) := by
  have hcont : ContinuousAt H 0 := hH.continuousOn.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hr))
  obtain ⟨ep,M,hep,hM,hloc⟩ := xrfcDFunction_compact_localization trial hhom base hb U hU hcount ht hT
    G H r hr hG₀ hH₀ hcont hG
  obtain ⟨R,hR⟩ := hU.exists_bound_of_continuousOn continuous_id.continuousOn
  let B := max R 1
  have hB : 0<B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨ep,(L:ℝ)/2*B^2+(L:ℝ)*M+1,hep,by positivity,?_⟩
  intro ε hε he u hu
  obtain ⟨hp,ho,_,_⟩ := hloc ε hε he u hu
  exact oneGradientFunction_source_bound (xrfcDMethod fullMemory trial) G H (cgOperator base) n
    hr hG₀ hH₀ hH hG M B hM.le ε hε u ((hR u hu).trans (le_max_left _ _)) hp ho

end
end krylov.Convergence
