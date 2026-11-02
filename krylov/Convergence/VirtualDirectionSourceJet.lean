import krylov.Convergence.VirtualDirectionReferenceComparison
import krylov.Convergence.OneGradientSourceJet

/-!
Article: main_krylov, thm:V and lem:cycle-transfer.
Use: derive the complete compatible first source jet for the true scalar
XRFC execution from original V1--V3. Every query enclosure and quadratic
shadow used by the transfer is proved internally from the actual policy.
Source: native XRFC localization, actual quadratic shadow and midpoint calculus.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Functions krylov.Nonlinear
  krylov.Stability
open scoped InnerProductSpace NNReal
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Original primitive hypotheses give the true full normalized source
jet uniformly on the original compact family, including the initial
gradient, every evaluated segment and the unevaluated output segment.
Article: main_krylov, thm:V and lem:cycle-transfer. -/
theorem xrfcDFunction_compact_source_jet
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
    (hG : ∀ x∈ball 0 r,HasFDerivAt G (H x) x)
    (D : E →L[ℝ] E →L[ℝ] E) (hD : HasFDerivAt H D 0) :
    ∀ η : ℝ,0<η →∃ ep : ℝ,0<ep ∧∀ ε : ℝ,0<ε →ε<ep →∀ u∈U,
      ‖oneGradientFunctionInput (xrfcDMethod fullMemory trial) G H (cgOperator base) ε u n-
        ε • oneGradientReferenceJet (xrfcDMethod fullMemory trial) (cgOperator base) D u n‖≤η*ε := by
  intro η hη
  obtain ⟨es,C,hes,hC,hshadow⟩ := xrfcDFunction_compact_reference_comparison trial hhom base hb U hU hcount ht hT
    G H r hr hG₀ hH₀ hH hG
  have hc : ContinuousAt H 0 := hH.continuousOn.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hr))
  obtain ⟨el,M,hel,hM,hloc⟩ := xrfcDFunction_compact_localization trial hhom base hb U hU hcount ht hT
    G H r hr hG₀ hH₀ hc hG
  obtain ⟨R,hR⟩ := hU.exists_bound_of_continuousOn continuous_id.continuousOn
  obtain ⟨ej,hej,hjet⟩ := oneGradientFunction_source_jet (xrfcDMethod fullMemory trial) G H (cgOperator base) D n
    hr hG₀ hH₀ hH.continuousOn hD hG M C (max R 1) hM hC.le
    (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) η hη
  refine ⟨min es (min el ej),by positivity,?_⟩
  intro ε hε he u hu
  have hs := hshadow ε hε (he.trans_le (min_le_left _ _)) u hu
  have hp := hloc ε hε (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))) u hu
  apply hjet ε hε (he.trans_le ((min_le_right _ _).trans (min_le_right _ _))) u
    ((hR u hu).trans (le_max_left _ _))
  · exact fun i hi=>by simpa only [mul_comm ε M,xrfcDFunctionPoint] using (hp.1 i hi).2
  · simpa only [mul_comm ε M,xrfcDFunctionOutput] using hp.2.1.2
  · exact hs.1
  · simpa only [xrfcDReferenceOutput_zero trial base hb u (hcount u hu) (ht u hu),smul_zero,sub_zero,xrfcDFunctionOutput] using hs.2

end
end krylov.Convergence
