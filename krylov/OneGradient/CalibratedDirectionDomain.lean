import krylov.OneGradient.CalibratedDirectionColumns
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), genuine complete native direction domain.
Use: derive the true chronological calibrated direction basis inverse from
full physical reference atoms, independently of perturbation estimates.
Source: actual positive reference replay model, real compression-domain
independence and the genuine finite chronological reversal equivalence.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.LinearAlgebra krylov.Correction
variable {X : Type*} [NormedAddCommGroup X] {n : ℕ}

/-- The actual chronological full calibrated direction basis has a genuine
inverse at every full-atom positive physical reference. No nonsingularity
or independence premise is imposed on the native replay arrays.
Use: the real cubic direction-output proof derives its full-model domain.
Article: main_krylov, thm:local(a), actual native direction inverse domain.
Proof: the real quadratic replay images are the true operator actions.
Its positive full latest model is therefore the genuine compression;
nonzero determinant gives independent native directions. Reverse the
actual newest-first family and assemble its true physical column matrix. -/
theorem calibrated_direction_columns_nonsingular
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hc : referenceAtomCount base hb g=n)
    (hcal : CalibratedTrial trial (cgOperator base) g (n))
    (A : X → ℕ → Matrix (Fin n) (Fin n) ℝ) (hA0 : ∀ k,A 0 k=base) :
    IsUnit (calibratedDirectionColumns trial A g 0).det := by
  let Q := cgOperator base
  let d := xrfcDExecutedDirection trial (fun _ => Q) g
  let D := fun i : Fin n => d (n-1-i.val)
  let Y := fun i : Fin n => xrfcDExecutedImage trial (fun _ => Q) g (n-1-i.val)
  have hp := cgOperator_positive base hb
  have hpre : ∀ i<n,CG.gradient Q g i≠0 := fun i hi => cg_nonstagnation base hb g i (by rw [hc];exact hi)
  have ht : ∀ i<n,trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => Q) g i)≠0 :=
    calibrated_native_reference_nonzero true trial Q hp.1 hp.2 g n hpre hcal
  have hY : Y=fun i => Q (D i) := by
    funext i
    dsimp only [Y,D,d]
    rw [xrfcD_executed_image_reference trial Q hp.1 hp.2 g n hpre ht _ (by omega),
      xrfcD_executed_direction_reference trial Q hp.1 hp.2 g n hpre ht _ (by omega)]
  have hdom := (xrfcD_full_array_domains trial Q hp.1 hp.2 g n hpre ht n le_rfl).2
  have hcomp : IsUnit (correctionCompression D Q).det := by
    rw [← pairModel_quadratic D Q hp.1,← hY]
    exact isUnit_iff_ne_zero.mpr hdom
  have hLI := compression_unit_independent D Q hcomp
  have hChron : LinearIndependent ℝ (fun i : Fin n => d i.val) := by
    have h := hLI.comp (Fin.revPerm (n := n)) (Fin.revPerm (n := n)).injective
    convert h using 1
    funext i
    change d i.val=d (n-1-i.rev.val)
    congr 1
    rw [Fin.val_rev]
    omega
  have hop0 : (fun k => cgOperator (A 0 k))=fun _ => Q := funext (fun k => congrArg cgOperator (hA0 k))
  change IsUnit (fullBasisMatrix (fun i : Fin n => xrfcDExecutedDirection trial (fun k => cgOperator (A 0 k)) g i.val)).det
  rw [hop0]
  exact fullBasisMatrix_unit _ hChron

end
end krylov.OneGradient
