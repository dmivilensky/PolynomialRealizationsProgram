import krylov.Convergence.EvaluatedSourceJet
import krylov.Convergence.EvaluatedOutputCoordinates

/-!
Article: main_krylov, prop:EL, true function transfer.
Use: obtain the full uniform quadratic leading term of the genuinely
executed scalar evaluated-launch cycle. The coefficient is independently defined by
the real finite operator derivative acting on the derived compatible
source jet. Its explicit flag representation is a subsequent dictionary.
Source: primitive C-two policy calculus and actual midpoint source jets.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Functions krylov.Nonlinear
  krylov.Stability
open scoped InnerProductSpace NNReal
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Genuine finite-operator derivative on the compatible tensor source
jet of the real quadratic query path. Article: prop:EL, cycle transfer. -/
def evaluatedLaunchFunctionLeadingCoefficient (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (D : E →L[ℝ] E →L[ℝ] E) (u : E) : E :=
  fderiv ℝ (oneGradientFiniteOutput (evaluatedLaunchMethod trial) Q n) (Q u,0)
    (oneGradientReferenceJet (evaluatedLaunchMethod trial) Q D u n)

/-- The actual scalar evaluated-launch gradient has its complete uniform quadratic
leading term under V1--V3 and genuine differentiability of the Hessian.
No native trajectory or output expansion is assumed.
Article: main_krylov, prop:EL and lem:cycle-transfer. -/
theorem evaluatedLaunchFunction_compact_leading_gradient
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
    (D : E →L[ℝ] E →L[ℝ] E) (hD : HasFDerivAt H D 0) :
    ∀ η : ℝ,0<η →∃ ep : ℝ,0<ep ∧∀ ε : ℝ,0<ε →ε<ep →∀ u∈U,
      ‖G (evaluatedLaunchFunctionOutput trial G (ε • u))-
        ε^2 • evaluatedLaunchFunctionLeadingCoefficient trial (cgOperator base) D u‖≤η*ε^2 := by
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
  have hjet := evaluatedLaunchFunction_compact_source_jet trial hhom base hb U hU hcount ht hT
    G H r hr hG₀ hH₀ hH hG D hD
  have htransfer := oneGradient_output_source_transfer m Q n U
    (fun ε u=>oneGradientFunctionInput m G H Q ε u n)
    (fun u=>oneGradientReferenceJet m Q D u n) K hK (fun u hu=>⟨u,hu,rfl⟩)
    hreg hzero S hS ⟨es,hes,fun ε hε he u hu=>(hsource ε hε he u hu).1⟩ hjet
  intro η hη
  obtain ⟨et,het,hbound⟩ := htransfer η hη
  refine ⟨min es et,lt_min hes het,?_⟩
  intro ε hε he u hu
  have hs := hsource ε hε (he.trans_le (min_le_left _ _)) u hu
  rw [evaluatedLaunchFunction_scaled_output trial hhom G H Q ε hε u hs.2.2]
  exact hbound ε hε (he.trans_le (min_le_right _ _)) u hu

end
end krylov.Convergence
