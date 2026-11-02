import krylov.OneGradient.CalibratedReferenceFlags
import krylov.OneGradient.InformedStaircase
import krylov.OneGradient.XRFCSharp
import krylov.Information.CentreModel
import krylov.Secant.Trajectory
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), actual native source staircase.
Use: identify the complete implemented leading operator and its terminal
pivot action with the original reusable orthogonal-CG staircase.
Source: genuine native flag dictionary, the true full final projector,
and actual canonical physical increment definitions.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Secant krylov.Stability
  krylov.Correction krylov.Envelope krylov.Variation krylov.Information
open scoped BigOperators InnerProductSpace
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X]

/-- The actual native calibrated leading operator is exactly the source
staircase in its genuine physical canonical increments.
Use: every existing sharp staircase estimate applies to actual S/D output.
Article: main_krylov, thm:local(a), native L equals the source L.
Proof: identify each true reference flag and its transpose with its
orthogonal projection. The complete final flag is identity; split off
its actual output increment and retain every earlier compressed increment. -/
theorem calibrated_native_launch_eq_staircase (directions : Bool)
    (trial : History (EuclideanSpace ℝ (Fin (n+1))) → ℝ)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1)
    (hcal : CalibratedTrial trial (cgOperator base) g (n+1))
    (A : X → ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA0 : ∀ j,A 0 j=base) (z : X) :
    calibratedNativeLaunchOperator directions trial base A g z=
      staircaseOperator base g (canonicalIncrement base (A z))
        (canonicalIncrement base (A z) n) (n+1) := by
  let P := fun l => transportedFlag
    (metricRoot base*calibratedNativeReferenceColumns directions trial A g) l
  have hP : ∀ l,cgOperator (P l)=(oldFlag base g l).starProjection :=
    calibrated_native_reference_flags directions trial base hb g hc hcal A hA0
  have hPt (l : ℕ) : cgOperator (P l)ᵀ=(oldFlag base g l).starProjection := by
    rw [cgOperator_transpose,hP]
    exact (Submodule.starProjection_isSymmetric _).clm_adjoint_eq
  change (∑ l∈range (n+1),cgOperator (P l)ᵀ*
    (cgOperator (metricRoot base)⁻¹*(cgOperator (A z (l+1))-cgOperator (A z l))*
      cgOperator (metricRoot base)⁻¹)*cgOperator (P l))=_
  simp_rw [hPt,hP,show ∀ l,cgOperator (metricRoot base)⁻¹*
      (cgOperator (A z (l+1))-cgOperator (A z l))*cgOperator (metricRoot base)⁻¹=
        cgOperator (canonicalIncrement base (A z) l) from fun l => by
    simp only [canonicalIncrement,relativeOperator,cgOperator,map_mul,map_sub]]
  rw [sum_range_succ,fullCG_last_projection base hb g hc,one_mul,mul_one]
  rfl

end
end krylov.OneGradient
