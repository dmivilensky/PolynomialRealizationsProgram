import krylov.OneGradient.InformedReferenceFlags
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

/-- The final genuine CG prefix projector is the actual identity on a
complete active frame.
Use: the last observed-to-output increment occurs uncompressed.
Article: main_krylov, thm:local(a), P_last=I.
Proof: the full canonical matrix is nonsingular and its final coordinate
selector is the identity, so its exact transported flag is the identity. -/
theorem fullCG_last_projection
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1) :
    (oldFlag base g n).starProjection=1 := by
  rw [← canonicalCG_transportedFlag base hb g hc n,transportedFlag,
    final_prefixProjection,Matrix.mul_one,
    Matrix.mul_nonsing_inv _ (canonicalCGUnitMatrix_unit base hb g hc)]
  exact map_one _

/-- The actual native informed leading operator is exactly the source
staircase in its genuine physical canonical increments.
Use: every existing sharp staircase estimate applies to actual S/D output.
Article: main_krylov, thm:local(a), native L equals the source L.
Proof: identify each true reference flag and its transpose with its
orthogonal projection. The complete final flag is identity; split off
its actual output increment and retain every earlier compressed increment. -/
theorem informed_native_launch_eq_staircase (directions : Bool)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1)
    (A : X → ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA0 : ∀ j,A 0 j=base) (z : X) :
    informedNativeLaunchOperator directions base A g z=
      staircaseOperator base g (canonicalIncrement base (A z))
        (canonicalIncrement base (A z) n) (n+1) := by
  let P := fun l => transportedFlag
    (metricRoot base*informedNativeReferenceColumns directions base A g) l
  have hP : ∀ l,cgOperator (P l)=(oldFlag base g l).starProjection :=
    informed_native_reference_flags directions base hb g hc A hA0
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

/-- The genuine source staircase acts on the actual terminal CG unit
step through only the independent output increment.
Use: recover the source's displayed epsilon times Eprime terminal term.
Article: main_krylov, thm:local(a), L h_last=Eprime h_last.
Proof: every genuine earlier orthogonal old flag annihilates the true
last unit step. Thus each real old compression vanishes exactly. -/
theorem staircase_terminal_unit
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1)
    (E : ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (F : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    staircaseOperator base g E F (n+1) (canonicalCGUnitStep base g n)=
      cgOperator F (canonicalCGUnitStep base g n) := by
  rw [staircaseOperator_apply]
  have hzero (l : ℕ) (hl : l∈range n) :
      (oldFlag base g l).starProjection (canonicalCGUnitStep base g n)=0 := by
    change ((oldFlag base g l).orthogonalProjectionOnto (canonicalCGUnitStep base g n) :
      EuclideanSpace ℝ (Fin (n+1)))=0
    rw [(oldFlag base g l).orthogonalProjectionOnto_eq_zero_iff.mpr
      (unitStep_prefix_oldFlag_orthogonal base hb g hc.ge (by omega) (mem_range.mp hl))]
    rfl
  simp only [Nat.add_sub_cancel]
  rw [sum_eq_zero (fun l hl => by rw [hzero l hl,map_zero,map_zero]),zero_add]

end
end krylov.OneGradient
