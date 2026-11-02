import krylov.Functions.NativeRFCFOwnTensorTransfer
import krylov.Functions.NativeRFCOwnSpatialResponse
import krylov.Functions.RFCFCanonicalQuadratic

/-!
Article: main_krylov, prop:Fcycle(i), actual own-A₀ corrected tensor response.
Use: identify the genuine native value-corrected coefficient in the canonical
metric of its actual first secant and independently observed initial gradient.
Source: actual raw diagonal compression, genuine reference differences and
exact nonsingular full-coordinate cancellation.
-/
namespace krylov.Functions
noncomputable section
open Set Metric Matrix Finset krylov.Methods krylov.Reference krylov.Nonlinear krylov.Correction
  krylov.Secant krylov.Variation krylov.Envelope
open scoped InnerProductSpace NNReal BigOperators Matrix.Norms.L2Operator
variable {k : ℕ}

/-- The original raw observed diagonal is exactly the compression of the genuine canonical half-step diagonal operator.
Article: main_krylov, prop:Fcycle(i), exact reversal and current-line scale cancellation. -/
theorem rfcFOwnReferenceRawValueChange_eq_compression
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (g : EuclideanSpace ℝ (Fin (k+1)))
    (hN : k+1≤referenceAtomCount base hb g) :
    rfcFOwnReferenceRawValueChange base D g=
      correctionCompression
        (fun i=>cgOperator (metricRoot base) (referenceModelBasis base g k i))
        (rfcFReferenceDiagonal base D g) := by
  ext i j
  change _=inner ℝ _ (rfcFReferenceDiagonal base D g _)
  dsimp only
  rw [referenceModelBasis_canonical base hb _ k hN i,referenceModelBasis_canonical base hb _ k hN j]
  simp only [map_smul,real_inner_smul_left,real_inner_smul_right]
  have hi : k-i.val=i.rev.val := by simp only [Fin.val_rev]; omega
  have hj : k-j.val=j.rev.val := by simp only [Fin.val_rev]; omega
  rw [hi,hj,rfcFReferenceDiagonal_step_pair base hb D _ hN i.rev j.rev]
  by_cases hij : i=j
  · subst j
    simp only [rfcFOwnReferenceRawValueChange,diagonal_apply_eq,↓reduceIte]
    have hscale : referenceBasisScale base g k i=
      ((Fin.cons (CG.length (cgOperator base) g k) (fun _ : Fin k=>(1:ℝ)) : Fin (k+1) → ℝ) i)⁻¹ := by
      refine Fin.cases rfl (fun j=>?_) i
      simp only [referenceBasisScale,Fin.cons_succ,inv_one]
    rw [hscale]
    ring
  · have hr : i.rev≠j.rev := fun he=>hij (Fin.rev_injective he)
    simp only [rfcFOwnReferenceRawValueChange,diagonal_apply_ne _ hij,ite_eq_right hr,mul_zero]
/-- The genuine corrected staircase and fresh defect in the observed
first-secant metric. Article: main_krylov, prop:Fcycle(i), Lambda_F. -/
def rfcFOwnTensorCanonicalCoefficient (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (g : EuclideanSpace ℝ (Fin (k+1))) : EuclideanSpace ℝ (Fin (k+1)) :=
  ‖canonicalCGStep base g k‖ •
    (staircaseOperator base g (ownFCCompatibleIncrements base hb D g)
      (rfcOwnCompatibleCorrection base hb D g) (k+1)-rfcFReferenceDiagonal base D g)
      (freshDefect base g (ownFCCompatibleIncrements base hb D g) (k+1))

/-- The true own-reference physical tensor coefficient has exactly the
printed original-A₀ canonical staircase/fresh-defect form, independently
of the unobserved initial-position offset.
Article: main_krylov, thm:Htransfer, original reference dictionary. -/
theorem rfcFOwnTensorPhysicalCoefficient_eq_canonical
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (g u : EuclideanSpace ℝ (Fin (k+1))) (hN : k+1≤referenceAtomCount base hb g) :
    cgOperator (metricRoot base)⁻¹ (rfcFOwnTensorPhysicalCoefficient base D g u)=
      rfcFOwnTensorCanonicalCoefficient base hb D g := by
  let A := fun i=>cgOperator base+D (fcOwnReferenceMidpoint (cgOperator base) g u i)
  let B := fun i=>cgOperator base+D (u+CG.displacement (cgOperator base) g (i+1))
  have hcoef : rfcFOwnTensorPhysicalCoefficient base D g u=rfcModifiedQuadratic base g A B (rfcFOwnReferenceRawValueChange base D g) := by
    apply rfcModifiedQuadratic_congr_prefix
    · intro j hj
      simp only [rfcOwnTensorSearch,ite_eq_left (by omega : j<k+1),A]
    · simp only [rfcOwnTensorCorrection,ite_eq_left (by omega : k<k+1),B]
  have hA l : A (l+1)-A l=D ((1/2:ℝ) • (referenceStep (cgOperator base) g l+referenceStep (cgOperator base) g (l+1))) := by
    simp only [A,add_sub_add_left_eq_sub,←map_sub,fcOwnReferenceMidpoint_sub]
  have hB : B k-A k=D ((1/2:ℝ) • referenceStep (cgOperator base) g k) := by
    have he : (u+CG.displacement (cgOperator base) g (k+1))-
        fcOwnReferenceMidpoint (cgOperator base) g u k=(1/2:ℝ) • referenceStep (cgOperator base) g k := by
      unfold fcOwnReferenceMidpoint
      rw [CG.displacement_succ]
      unfold referenceStep
      module
    simp only [B,A,add_sub_add_left_eq_sub,←map_sub,he]
  rw [hcoef,rfcModifiedQuadratic_eq_canonical base hb g hN _ _ _ _
    (rfcFOwnReferenceRawValueChange_eq_compression base hb D g hN)]
  simp only [hA,hB]
  rfl


end
end krylov.Functions
