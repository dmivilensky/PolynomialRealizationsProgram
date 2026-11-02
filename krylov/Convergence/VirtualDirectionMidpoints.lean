import krylov.Convergence.VirtualDirectionTensorCoordinates
import krylov.Convergence.VirtualReferenceMidpoints

/-!
Article: main_krylov, thm:V, direction-basis reference midpoint dictionary.
Use: identify its real compatible displacements with the same explicit
xi_l of the original quadratic reference. Source: actual equality of the
two native quadratic transcripts and true virtual CG termination.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set krylov.Methods krylov.Reference krylov.Functions krylov.OneGradient krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Both actual quadratic executors have identical reference segment
midpoints and hence identical genuine compatible midpoint displacements.
Article: main_krylov, thm:V, the same xi_l in either stored basis. -/
theorem xrfcDReferenceMidpointDrift_eq_step
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (u : E) (hc : referenceAtomCount base hb (cgOperator base u)=n)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcDMethod fullMemory trial)
      (fun _=>cgOperator base) (cgOperator base u) i)≠0) (l : ℕ) :
    xrfcDReferenceMidpointDrift trial (cgOperator base) u l=
      xrfcReferenceMidpointDrift trial (cgOperator base) u l := by
  let Q:=cgOperator base
  have hpre i (hi : i<n) := cg_nonstagnation base hb (Q u) i (by rw [hc];exact hi)
  have hhist (i : ℕ) (hi : i≤n) := xrfc_quadratic_basis_histories_of_direction trial Q
    (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 (Q u) n hpre ht i hi
  have hpoint (i : ℕ) (hi : i≤n) :
      oneGradientReferencePoint (xrfcDMethod fullMemory trial) Q u i=
        oneGradientReferencePoint (xrfcMethod fullMemory trial) Q u i := by
    unfold oneGradientReferencePoint
    rw [hhist i hi]
  have hout : oneGradientReferenceOutput (xrfcDMethod fullMemory trial) Q u n=
      oneGradientReferenceOutput (xrfcMethod fullMemory trial) Q u n := by
    have hD:=(xrfcD_reference fullMemory trial Q (cgOperator_positive base hb).1
      (cgOperator_positive base hb).2 (Q u) n hpre (fun _ _ hi=>hi) ht n le_rfl).1
    have hS:=(xrfc_full_reference trial Q (cgOperator_positive base hb).1
      (cgOperator_positive base hb).2 (Q u) n hpre
      (fun i hi=>by rw [←hhist i hi.le];exact ht i hi) n le_rfl).1
    unfold oneGradientReferenceOutput oneGradientReferencePoint
    simp only [add_assoc]
    change u+ (xrfcDMethod fullMemory trial).outputDisplacement _=u+(xrfcMethod fullMemory trial).outputDisplacement _
    rw [hD,hS]
  have hmid (i : ℕ) : oneGradientReferenceMidpoint (xrfcDMethod fullMemory trial) Q u n i=
      oneGradientReferenceMidpoint (xrfcMethod fullMemory trial) Q u n i := by
    unfold oneGradientReferenceMidpoint
    split_ifs with hi
    · rw [hpoint i hi.le,hpoint (i+1) (by omega)]
    · rw [hpoint n le_rfl,hout]
  change oneGradientReferenceMidpoint _ Q u n (l+1)-oneGradientReferenceMidpoint _ Q u n l=_
  rw [hmid,hmid]
  rfl

end
end krylov.Convergence
