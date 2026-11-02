import krylov.Convergence.EvaluatedLeadingGradient
import krylov.Convergence.EvaluatedSourceQuadratic
import krylov.Convergence.OneGradientCubicTransfer

/-!
Article: main_krylov, prop:EL, Lipschitz-third conclusion.
Use: prove the actual evaluated-launch output gradient has a uniform cubic remainder
about its independently defined genuine finite-operator tensor coefficient.
Source: true source-jet calculus and compact C-two policy Taylor estimates.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Functions krylov.Nonlinear
  krylov.Stability
open scoped InnerProductSpace NNReal
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Original V1--V3 and genuine local Lipschitz D3 give an O(e³)
remainder in the real returned gradient at the unevaluated output.
Article: main_krylov, prop:EL. -/
theorem evaluatedLaunchFunction_compact_cubic_remainder
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
    ∃ ep C : ℝ,0<ep ∧0<C ∧∀ ε : ℝ,0<ε →ε<ep →∀ u∈U,
      ‖G (evaluatedLaunchFunctionOutput trial G (ε • u))-
        ε^2 • evaluatedLaunchFunctionLeadingCoefficient trial (cgOperator base) (D 0) u‖≤C*ε^3 := by
  let m := evaluatedLaunchMethod trial
  let Q := cgOperator base
  let K := Q '' U
  have hK : IsCompact K := hU.image Q.continuous
  have hreg : ∀ g∈K,ContDiffAt ℝ 2 (oneGradientFiniteOutput m Q n) (g,0) := by
    rintro g ⟨u,hu,rfl⟩
    exact evaluatedLaunchFiniteOutput_contDiffAt trial Q (cgOperator_positive base hb).1
      (cgOperator_positive base hb).2 n (Q u)
      (fun i hi=>cg_nonstagnation base hb (Q u) i (by rw [hcount u hu];exact hi))
      (fun i hi=>(ht u hu i hi).ne') (hT u hu)
  have hzero : ∀ g∈K,oneGradientFiniteOutput m Q n (g,0)=0 := by
    rintro g ⟨u,hu,rfl⟩
    exact evaluatedLaunchFiniteOutput_reference_zero trial base hb (Q u) (hcount u hu) (fun i hi=>(ht u hu i hi).ne')
  obtain ⟨es,S,hes,hS,hsource⟩ := evaluatedLaunchFunction_compact_source_inputs trial hhom base hb U hU hcount ht hT
    G H r hr hG₀ hH₀ hH hG
  have hjet := evaluatedLaunchFunction_compact_source_quadratic_jet trial hhom base hb U hU hcount ht hT
    G H r hr hG₀ hH₀ hH hG D hD hL₃
  have htransfer := oneGradient_output_source_cubic_transfer m Q n U
    (fun ε u=>oneGradientFunctionInput m G H Q ε u n)
    (fun u=>oneGradientReferenceJet m Q (D 0) u n) K hK (fun u hu=>⟨u,hu,rfl⟩)
    hreg hzero S hS ⟨es,hes,fun ε hε he u hu=>(hsource ε hε he u hu).1⟩ hjet
  obtain ⟨et,C,het,hC,hbound⟩ := htransfer
  refine ⟨min es et,C,lt_min hes het,hC,?_⟩
  intro ε hε he u hu
  have hs := hsource ε hε (he.trans_le (min_le_left _ _)) u hu
  rw [evaluatedLaunchFunction_scaled_output trial hhom G H Q ε hε u hs.2.2]
  exact hbound ε hε (he.trans_le (min_le_right _ _)) u hu


end
end krylov.Convergence
