import krylov.Convergence.EvaluatedReferenceComparison
import krylov.Convergence.OneGradientSourceQuadratic

/-!
Article: main_krylov, prop:EL, Lipschitz-third source transfer.
Use: derive a uniform quadratic full source remainder from the actual
Lipschitz third derivative and original V1--V3, with all real queries and
midpoint shadows proved internally.
Source: genuine native localization and Bochner midpoint calculus.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Functions krylov.Nonlinear
  krylov.Stability
open scoped InnerProductSpace NNReal
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The true entire evaluated-launch source has an O(e²) compatible tensor jet
remainder under the actual local Lipschitz D3 hypothesis. Article: prop:EL. -/
theorem evaluatedLaunchFunction_compact_source_quadratic_jet
    (trial : History E → ℝ) (hhom : ObservedTrialHomogeneous trial)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (U : Set E) (hU : IsCompact U)
    (hcount : ∀ u∈U,referenceAtomCount base hb (cgOperator base u)=n)
    (ht : ∀ u∈U,∀ i<n,0<trial (oneGradientRun (evaluatedLaunchMethod trial)
      (fun _=>cgOperator base) (cgOperator base u) i))
    (hT : ∀ u∈U,∀ i<n,ContDiffAt ℝ 2 (trialCoordinate trial i)
      (oneGradientData (evaluatedLaunchMethod trial) (fun _=>cgOperator base) (cgOperator base u) i))
    (G : E → E) (H : E → E →L[ℝ] E) (r : ℝ) (hr : 0<r)
    (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base) {L : ℝ≥0} (hH : LipschitzOnWith L H (ball 0 r))
    (hG : ∀ x∈ball 0 r,HasFDerivAt G (H x) x)
    (D : E → E →L[ℝ] E →L[ℝ] E)
    (hD : ∀ z∈ball 0 r,HasFDerivAt H (D z) z)
    {L₃ : ℝ≥0} (hL₃ : LipschitzOnWith L₃ D (ball 0 r)) :
    ∃ ep J : ℝ,0<ep ∧0<J ∧∀ ε : ℝ,0<ε →ε<ep →∀ u∈U,
      ‖oneGradientFunctionInput (evaluatedLaunchMethod trial) G H (cgOperator base) ε u n-
        ε • oneGradientReferenceJet (evaluatedLaunchMethod trial) (cgOperator base) (D 0) u n‖≤J*ε^2 := by
  obtain ⟨es,C,hes,hC,hshadow⟩ := evaluatedLaunchFunction_compact_reference_comparison trial hhom base hb U hU hcount ht hT
    G H r hr hG₀ hH₀ hH hG
  have hc : ContinuousAt H 0 := hH.continuousOn.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hr))
  obtain ⟨el,M,hel,hM,hloc⟩ := evaluatedLaunchFunction_compact_localization trial hhom base hb U hU hcount ht hT
    G H r hr hG₀ hH₀ hc hG
  obtain ⟨R,hR⟩ := hU.exists_bound_of_continuousOn continuous_id.continuousOn
  have hsub : closedBall (0:E) (r/2)⊆ball 0 r := by
    intro z hz
    rw [mem_closedBall,dist_zero_right] at hz
    rw [mem_ball,dist_zero_right]
    exact hz.trans_lt (by linarith only [hr])
  obtain ⟨ej,J,hej,hJ,hjet⟩ := oneGradientFunction_source_quadratic_jet (evaluatedLaunchMethod trial)
    G H (cgOperator base) D n (half_pos hr) hG₀ hH₀
    (fun z hz=>hG z (hsub hz)) (fun z hz=>hD z (hsub hz)) (hL₃.mono hsub)
    M C (max R 1) hM hC.le (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  refine ⟨min es (min el ej),J,by positivity,hJ,?_⟩
  intro ε hε he u hu
  have hs := hshadow ε hε (he.trans_le (min_le_left _ _)) u hu
  have hp := hloc ε hε (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))) u hu
  apply hjet ε hε (he.trans_le ((min_le_right _ _).trans (min_le_right _ _))) u
    ((hR u hu).trans (le_max_left _ _))
  · exact fun i hi=>by simpa only [mul_comm ε M,evaluatedLaunchFunctionPoint] using (hp.1 i hi).2
  · simpa only [mul_comm ε M,evaluatedLaunchFunctionOutput] using hp.2.1.2
  · exact hs.1
  · simpa only [evaluatedLaunchReferenceOutput_zero trial base hb u (hcount u hu) (ht u hu),smul_zero,sub_zero,evaluatedLaunchFunctionOutput] using hs.2


end
end krylov.Convergence
