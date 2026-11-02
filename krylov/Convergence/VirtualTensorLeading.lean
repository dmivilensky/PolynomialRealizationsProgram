import krylov.Convergence.VirtualTensorBound

/-!
Article: main_krylov, thm:V, literal true-gradient formula.
Use: expose the actual minimizer-dual-metric gradient at the genuine
unevaluated scalar XRFC output with the explicit source flag/tensor
coefficient and a compact-uniform little-o quadratic remainder.
Source: genuine native function transfer and the exact operator/tensor dictionary.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Functions krylov.Nonlinear
  krylov.Stability krylov.OneGradient krylov.Secant
open scoped InnerProductSpace NNReal
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The actual scalar XRFC output satisfies the original canonical
quadratic-gradient expansion with its explicit true oblique tensor sum.
All symmetry and query domains come from the original scalar derivatives.
Article: main_krylov, thm:V, step-basis formula. -/
theorem xrfcFunction_compact_tensor_leading_gradient
    (trial : History E → ℝ) (hhom : ObservedTrialHomogeneous trial)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (U : Set E) (hU : IsCompact U)
    (hcount : ∀ u∈U,referenceAtomCount base hb (cgOperator base u)=n)
    (ht : ∀ u∈U,∀ i<n,0<trial (oneGradientRun (xrfcMethod fullMemory trial)
      (fun _=>cgOperator base) (cgOperator base u) i))
    (hT : ∀ u∈U,∀ i<n,ContDiffAt ℝ 2 (trialCoordinate trial i)
      (oneGradientData (xrfcMethod fullMemory trial) (fun _=>cgOperator base) (cgOperator base u) i))
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (r : ℝ) (hr : 0<r)
    (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base) {L : ℝ≥0} (hH : LipschitzOnWith L H (ball 0 r))
    (hF : ∀ x∈ball 0 r,HasFDerivAt f (innerSL ℝ (G x)) x)
    (hG : ∀ x∈ball 0 r,HasFDerivAt G (H x) x)
    (D : E →L[ℝ] E →L[ℝ] E) (hD : HasFDerivAt H D 0) (hn : 0<n) :
    ∀ η : ℝ,0<η →∃ ep : ℝ,0<ep ∧∀ ε : ℝ,0<ε →ε<ep →∀ u∈U,
      ‖cgOperator (metricRoot base)⁻¹ (G (xrfcFunctionOutput trial G (ε • u)))-
        ε^2 • xrfcTensorCoefficient trial base D u‖≤η*ε^2 := by
  intro η hη
  let R := cgOperator (metricRoot base)⁻¹
  obtain ⟨ep,hep,hbound⟩ := xrfcFunction_compact_leading_gradient trial hhom base hb U hU hcount ht hT
    G H r hr hG₀ hH₀ hH hG D hD (η/(‖R‖+1)) (by positivity)
  refine ⟨ep,hep,?_⟩
  intro ε hε he u hu
  have hcoeff := xrfcFunctionLeadingCoefficient_eq_tensor_genuine trial base hb f G H D hD hr hF hG
    u (hcount u hu) hn (fun i hi=>(ht u hu i hi).ne') (hT u hu)
  rw [←hcoeff,←map_smul,←map_sub]
  have hbnd := (R.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hbound ε hε he u hu) (norm_nonneg _))
  apply hbnd.trans
  have hh : (‖R‖+1)*(η/(‖R‖+1))=η := by field_simp
  have hm : 0≤η/(‖R‖+1)*ε^2 := by positivity
  nlinarith only [congrArg (fun a : ℝ=>a*ε^2) hh,hm]

end
end krylov.Convergence
