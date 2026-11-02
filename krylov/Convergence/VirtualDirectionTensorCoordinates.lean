import krylov.Convergence.VirtualDirectionDerivativeCoordinates
import krylov.Convergence.VirtualDirectionLeadingGradient
import krylov.Convergence.VirtualTensorCoordinates
import krylov.Convergence.OneGradientSymmetry
import krylov.Functions.GenuineHessianSymmetry

/-!
Article: main_krylov, thm:V, actual tensor coefficient.
Use: identify the true scalar-cycle leading coefficient with the printed
oblique-flag response on genuine third-derivative midpoint differences.
Source: full joint operator derivative, scalar Schwarz symmetry and true
quadratic-reference segment midpoints.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric krylov.Methods krylov.Reference krylov.Functions krylov.Stability krylov.OneGradient
  krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The source's true compatible midpoint difference, in physical
coordinates before applying the minimizer root. Article: thm:V. -/
def xrfcDReferenceMidpointDrift (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (u : E) (i : ℕ) : E :=
  oneGradientReferenceMidpoint (xrfcDMethod fullMemory trial) Q u n (i+1)-
    oneGradientReferenceMidpoint (xrfcDMethod fullMemory trial) Q u n i

/-- The printed actual XRFC coefficient with its true oblique flags,
measured amplitudes and compatible third-derivative midpoint slices.
Article: main_krylov, thm:V. -/
def xrfcDTensorCoefficient (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ)
    (D : E →L[ℝ] E →L[ℝ] E) (u : E) : E :=
  let R := cgOperator (metricRoot base)⁻¹
  xrfcDirectionResponse trial base (cgOperator base u)
    (fun l=>R*(D (xrfcDReferenceMidpointDrift trial (cgOperator base) u l))*R)

/-- The complete compatible source derivative is exactly the printed
oblique response. Every tensor slice is actual; arbitrary initial-gradient
drift is included and contributes no additional term.
Article: main_krylov, thm:V. -/
theorem xrfcDFunctionLeadingCoefficient_eq_tensor
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (D : E →L[ℝ] E →L[ℝ] E) (_hsym : ∀ v,(D v).toLinearMap.IsSymmetric)
    (u : E) (hc : referenceAtomCount base hb (cgOperator base u)=n) (hn : 0<n)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _=>cgOperator base) (cgOperator base u) i)≠0)
    (hT : ∀ i<n,ContDiffAt ℝ 2 (trialCoordinate trial i)
      (oneGradientData (xrfcDMethod fullMemory trial) (fun _=>cgOperator base) (cgOperator base u) i)) :
    cgOperator (metricRoot base)⁻¹ (xrfcDFunctionLeadingCoefficient trial (cgOperator base) D u)=
      xrfcDTensorCoefficient trial base D u := by
  let m := xrfcDMethod fullMemory trial
  let Q := cgOperator base
  let z := oneGradientReferenceJet m Q D u n
  have hh := xrfcDFiniteOutput_fderiv_response trial base hb (Q u) hc hn ht hT z
  have hW (i : ℕ) : oneGradientOutputDrift n z.2.1 z.2.2 i=D (oneGradientReferenceMidpoint m Q u n i) := by
    dsimp only [oneGradientOutputDrift,oneGradientReferenceMidpoint,z,oneGradientReferenceJet]
    split_ifs <;> rfl
  change _=xrfcDirectionResponse trial base (Q u) _
  simpa only [hW,←map_sub,xrfcDFunctionLeadingCoefficient,xrfcDReferenceMidpointDrift] using hh

/-- Actual scalar derivatives on the original open ball discharge the
slice-symmetry premise in the printed coefficient dictionary.
Article: main_krylov, thm:V and lem:cycle-transfer. -/
theorem xrfcDFunctionLeadingCoefficient_eq_tensor_genuine
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (D : E →L[ℝ] E →L[ℝ] E) (hD : HasFDerivAt H D 0) {r : ℝ} (hr : 0<r)
    (hF : ∀ z∈ball 0 r,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈ball 0 r,HasFDerivAt G (H z) z)
    (u : E) (hc : referenceAtomCount base hb (cgOperator base u)=n) (hn : 0<n)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _=>cgOperator base) (cgOperator base u) i)≠0)
    (hT : ∀ i<n,ContDiffAt ℝ 2 (trialCoordinate trial i)
      (oneGradientData (xrfcDMethod fullMemory trial) (fun _=>cgOperator base) (cgOperator base u) i)) :
    cgOperator (metricRoot base)⁻¹ (xrfcDFunctionLeadingCoefficient trial (cgOperator base) D u)=
      xrfcDTensorCoefficient trial base D u := by
  have hs v := genuine_third_slice_symmetric (ContinuousLinearEquiv.refl ℝ E) f G H D hD (half_pos hr)
    (fun z hz=>hF z (by rw [mem_ball,dist_zero_right];exact hz.trans_lt (by linarith only [hr])))
    (fun z hz=>hG z (by rw [mem_ball,dist_zero_right];exact hz.trans_lt (by linarith only [hr]))) v
  exact xrfcDFunctionLeadingCoefficient_eq_tensor trial base hb D hs u hc hn ht hT

end
end krylov.Convergence
