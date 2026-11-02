import krylov.Convergence.VirtualTensorLeading
import krylov.Convergence.VirtualCubicRemainder

/-!
Article: main_krylov, thm:V, printed tensor formula with cubic remainder.
Use: state the genuine minimizer-dual-gradient expansion at the actual
scalar XRFC output with exactly the explicit oblique tensor coefficient.
Source: actual native Lipschitz-third transfer and scalar tensor symmetry.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Functions krylov.Nonlinear
  krylov.Stability krylov.OneGradient krylov.Secant
open scoped InnerProductSpace NNReal
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Genuine scalar XRFC has the source's explicit canonical tensor
coefficient and a uniform O(e³) remainder under actual Lipschitz D3.
Article: main_krylov, thm:V, step-basis formula. -/
theorem xrfcFunction_compact_tensor_cubic_remainder
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
    (D : E → E →L[ℝ] E →L[ℝ] E)
    (hD : ∀ z∈ball 0 r,HasFDerivAt H (D z) z)
    {L₃ : ℝ≥0} (hL₃ : LipschitzOnWith L₃ D (ball 0 r)) (hn : 0<n) :
    ∃ ep C : ℝ,0<ep ∧0<C ∧∀ ε : ℝ,0<ε →ε<ep →∀ u∈U,
      ‖cgOperator (metricRoot base)⁻¹ (G (xrfcFunctionOutput trial G (ε • u)))-
        ε^2 • xrfcTensorCoefficient trial base (D 0) u‖≤C*ε^3 := by
  let R := cgOperator (metricRoot base)⁻¹
  obtain ⟨ep,C,hep,hC,hbound⟩ := xrfcFunction_compact_cubic_remainder trial hhom base hb U hU hcount ht hT
    G H r hr hG₀ hH₀ hH hG D hD hL₃
  refine ⟨ep,‖R‖*C+1,hep,by positivity,?_⟩
  intro ε hε he u hu
  have hcoeff := xrfcFunctionLeadingCoefficient_eq_tensor_genuine trial base hb f G H (D 0)
    (hD 0 (mem_ball_self hr)) hr hF hG u (hcount u hu) hn
    (fun i hi=>(ht u hu i hi).ne') (hT u hu)
  rw [←hcoeff,←map_smul,←map_sub]
  have hbnd := (R.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hbound ε hε he u hu) (norm_nonneg _))
  exact hbnd.trans (by nlinarith only [show 0≤ε^3 by positivity])


end
end krylov.Convergence
