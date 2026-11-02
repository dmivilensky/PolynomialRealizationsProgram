import krylov.Correction.GatedExecution

/-!
Article: main_krylov, def:GRFC, exact positive common operator scaling.
Use: preserve the actual spectral and defect decisions when Hessian units
change, with inverse scaling of real displacements and unchanged gradients.
Source: totalized matrix-inverse scalar covariance, actual diagonal column
congruence invariance and the genuine exact-search and correction executors.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Scaling only the real stored displacements preserves their computed FC direction.
Use: operator scaling changes old step lengths but retains actual secants and gradients.
Article: main_krylov, def:GRFC, common operator units in the direction solve.
Proof: the true cross Gram acquires one factor c; its inverse contributes
c⁻¹, which cancels the factor c in the actual synthesized old steps. -/
theorem conjugacyDirection_step_scalar {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s y : ι → E) (g : E) (c : ℝ) (hc : c≠0) :
    conjugacyDirection (fun i => c • s i) y g=conjugacyDirection s y g := by
  -- Keep the observed image family fixed while cancelling the true step-coordinate change.
  have hG : crossGram y (fun i => c • s i)=c • crossGram y s := by
    ext i j
    simp only [crossGram,real_inner_smul_right,Matrix.smul_apply,smul_eq_mul]
  have hcoef : conjugacyCoefficients (fun i => c • s i) y g=
      c⁻¹ • conjugacyCoefficients s y g := by
    rw [conjugacyCoefficients,hG,matrix_inv_scalar,smul_mulVec]
    rfl
  rw [conjugacyDirection,hcoef,combine_scalar]
  have hcomb : combine s (c⁻¹ • conjugacyCoefficients s y g)=
      c⁻¹ • combine s (conjugacyCoefficients s y g) := by
    simp only [combine,Pi.smul_apply,smul_eq_mul,smul_smul,Finset.smul_sum]
  rw [hcomb,smul_smul,mul_inv_cancel₀ hc,one_smul]
  rfl

/-- The measured normalized defect is unchanged when only actual stored steps are rescaled positively.
Use: common positive operator scaling preserves the real RFC defect gate.
Article: main_krylov, def:GRFC, positive operator scale and canonical defect.
Proof: numerator pairings acquire c and the actual diagonal-product square
root acquires the same positive c, even for zero or negative diagonal products. -/
theorem pairDefect_step_scalar {p : ℕ} (s y : Fin p → E) {c : ℝ} (hc : 0<c) :
    pairDefect (fun i => c • s i) y=pairDefect s y := by
  -- The normalized observation formula is valid on every actual gate branch.
  have hs (a b : ℝ) : Real.sqrt ((c*a)*(c*b))=c*Real.sqrt (a*b) := by
    rw [show (c*a)*(c*b)=c^2*(a*b) by ring,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hc.le]
  ext i j
  simp only [pairDefect,real_inner_smul_left,hs]
  rw [← mul_sub,mul_div_mul_left _ _ hc.ne']

/-- An actual model correction scales inversely with a common operator factor in its model.
Use: combine true operator-unit changes with independent actual column normalizations.
Article: main_krylov, def:GRFC, inverse model scaling.
Proof: the totalized finite inverse contributes c⁻¹ and physical synthesis is linear in its coefficients. -/
theorem modelCorrection_model_scalar {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → E) (H : Matrix ι ι ℝ) (g : E) (c : ℝ) :
    combine s (modelCoefficients s (c • H) g)=c⁻¹ • combine s (modelCoefficients s H g) := by
  simp only [modelCoefficients,matrix_inv_scalar,smul_mulVec,neg_smul,combine,
    Pi.smul_apply,smul_eq_mul,Pi.neg_apply,Finset.smul_sum,mul_smul,smul_neg]

/-- The true exact-search length scales inversely with a nonzero common probe factor.
Use: actual line displacements transform before any correction is executed.
Article: main_krylov, def:GRFC, A↦cA exact-search covariance.
Proof: factor c out of the observed curvature denominator, retaining totalized zero divisions. -/
theorem lineLength_probe_scalar (g d z : E) (c : ℝ) :
    lineLength g d (c • z)=c⁻¹*lineLength g d z := by
  simp only [lineLength,real_inner_smul_right,div_eq_mul_inv,_root_.mul_inv_rev]
  ring

/-- The true post-search gradient is unchanged by a nonzero common probe factor.
Use: all actual correction right-hand sides remain unchanged under operator scaling.
Article: main_krylov, def:GRFC, common operator-unit covariance.
Proof: the reciprocal line-length factor cancels its actual probe factor. -/
theorem searchedGradient_probe_scalar (g d z : E) (c : ℝ) (hc : c≠0) :
    searchedGradient g d (c • z)=searchedGradient g d z := by
  rw [searchedGradient,lineLength_probe_scalar,smul_smul]
  have he : (c⁻¹*lineLength g d z)*c=lineLength g d z := by
    rw [mul_right_comm,inv_mul_cancel₀ hc,one_mul]
  rw [he]
  rfl

/-- The augmented actual model transforms by its exact mixed current/old-column congruence.
Use: common operator scaling keeps the current direction fixed while old total steps scale inversely.
Article: main_krylov, def:GRFC, real augmented H covariance.
Proof: old images acquire c times their inverse column scale, and the current
probe acquires c; bilinearity gives cDHD with D=diag(1,c⁻¹,…,c⁻¹). -/
theorem augmentedModel_curvature_scalar {p : ℕ} (s y : Fin p → E) (d z : E)
    (c : ℝ) (hc : c≠0) :
    pairModel (Fin.cons d (fun i => c⁻¹ • s i)) (Fin.cons (c • z) y)=
      c • rescaleModel (pairModel (Fin.cons d s) (Fin.cons z y))
        (Fin.cons 1 (fun _ => c⁻¹)) := by
  -- Express both true augmented families in the same individual column coordinates.
  have hu : (Fin.cons d (fun i => c⁻¹ • s i) : Fin (p+1) → E)=
      rescaleWindow (Fin.cons d s) (Fin.cons 1 (fun _ => c⁻¹)) := by
    funext i
    refine Fin.cases (by simp only [rescaleWindow,Fin.cons_zero,one_smul]) (fun _ => rfl) i
  have hz : (Fin.cons (c • z) y : Fin (p+1) → E)=fun i =>
      c • rescaleWindow (Fin.cons z y) (Fin.cons 1 (fun _ => c⁻¹)) i := by
    funext i
    refine Fin.cases (by simp only [rescaleWindow,Fin.cons_zero,one_smul]) (fun j => ?_) i
    simp only [rescaleWindow,Fin.cons_succ,smul_smul,mul_inv_cancel₀ hc,one_smul]
  have hp (u v : Fin (p+1) → E) : pairModel u (fun i => c • v i)=c • pairModel u v := by
    ext i j
    simp only [pairModel,real_inner_smul_right,Matrix.smul_apply,smul_eq_mul]
  rw [hu,hz,hp,pairModel_rescale]

/-- The actual augmented physical model correction scales inversely under a common nonzero operator factor.
Use: the mixed current/old window scaling is discharged for the genuine executed correction vector.
Article: main_krylov, def:GRFC, real correction covariance.
Proof: identify the actual augmented diagonal coordinate change, factor
the common operator scale out of the true inverse and cancel the invertible
column congruence using the previously proved actual model-correction identity. -/
theorem augmentedCorrection_curvature_scalar {p : ℕ} (s y : Fin p → E) (d z g : E)
    (c : ℝ) (hc : c≠0) :
    let U : Fin (p+1) → E := Fin.cons d s
    let Z : Fin (p+1) → E := Fin.cons z y
    let V : Fin (p+1) → E := Fin.cons d (fun i => c⁻¹ • s i)
    combine V (modelCoefficients V (pairModel V (Fin.cons (c • z) y)) g)=
      c⁻¹ • combine U (modelCoefficients U (pairModel U Z) g) := by
  -- Only the actual column diagonal must be nonsingular; the totalized model may be singular.
  dsimp only
  rw [augmentedModel_curvature_scalar s y d z c hc,modelCorrection_model_scalar]
  have hu : (Fin.cons d (fun i => c⁻¹ • s i) : Fin (p+1) → E)=
      rescaleWindow (Fin.cons d s) (Fin.cons 1 (fun _ => c⁻¹)) := by
    funext i
    refine Fin.cases (by simp only [rescaleWindow,Fin.cons_zero,one_smul]) (fun _ => rfl) i
  rw [hu,modelCorrection_rescale]
  rw [det_diagonal,isUnit_iff_ne_zero]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact Fin.cases one_ne_zero (fun _ => inv_ne_zero hc) i

end
end krylov.Correction
