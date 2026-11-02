import krylov.Methods.DirectionExecution
set_option autoImplicit false
/-!
Article: main_krylov, thm:I, exact original direction-image error recursion.
Use: derive the genuine replay error before differentiating the actual
varying-prefix XRFC-D output; no operator-image correctness is assumed.
Source: the real returned-gradient update, native latest-information virtual
coefficients and the original data-only inverse-trial replay formula.
-/

namespace krylov.Methods
noncomputable section
open Matrix
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The native actual full-memory direction-basis virtual coefficients.
Use: their reference sparsity will be proved from actual quadratic consistency.
Article: main_krylov, thm:I, w_(k,i). -/
def xrfcDArrayCoefficients (trial : History E → ℝ) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) : Fin k → ℝ :=
  let D := fun i : Fin k => xrfcDExecutedDirection trial A g (k-1-i.val)
  let Q := fun i : Fin k => xrfcDExecutedImage trial A g (k-1-i.val)
  modelCoefficients D (pairModel D Q) (oneGradientGradient (xrfcDMethod fullMemory trial) A g k)

/-- The genuine difference between an observed replay image and the actual
current segment-operator image of its executed direction.
Use: this error is zero on quadratic reference data, not on varying prefixes.
Article: main_krylov, thm:I, iota_k=q_k-A_k d_k. -/
def xrfcDImageError (trial : History E → ℝ) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) : E :=
  xrfcDExecutedImage trial A g k-A k (xrfcDExecutedDirection trial A g k)

/-- The original data-only XRFC-D replay satisfies exactly its true image-error
recursion on arbitrary varying segment operators and every actual nonzero trial.
Use: differentiate a real identity instead of postulating the printed first jet.
Article: main_krylov, thm:I, tau_j iota_j=sum_i w_ji ((A_j-A_i)d_i-iota_i).
Proof: substitute the actual returned gradient and the native virtual correction
and gradient into the observed inverse-trial image. Cancel the true nonzero
trial, distribute the actual finite physical combinations, and separate each
older segment drift from its genuine earlier replay error. -/
theorem xrfcD_image_error_recursion (trial : History E → ℝ) (A : ℕ → E →L[ℝ] E)
    (g : E) (k : ℕ)
    (ht : trial (oneGradientRun (xrfcDMethod fullMemory trial) A g k)≠0) :
    trial (oneGradientRun (xrfcDMethod fullMemory trial) A g k) • xrfcDImageError trial A g k=
      ∑ i : Fin k,xrfcDArrayCoefficients trial A g k i •
        ((A k-A (k-1-i.val)) (xrfcDExecutedDirection trial A g (k-1-i.val))-
          xrfcDImageError trial A g (k-1-i.val)) := by
  let m := xrfcDMethod fullMemory trial
  let H := oneGradientRun m A g k
  let tau := trial H
  let D := fun i : Fin k => xrfcDExecutedDirection trial A g (k-1-i.val)
  let Q := fun i : Fin k => xrfcDExecutedImage trial A g (k-1-i.val)
  let w := xrfcDArrayCoefficients trial A g k
  let d := xrfcDExecutedDirection trial A g k
  let c := virtualCorrection (xrfcDWindow trial A g k) H.gradient
  have hv := xrfcD_virtual_coordinates trial A g k
  have hc : c=combine D w := hv.1
  have hgv : xrfcDVirtualGradient trial A g k=H.gradient+combine Q w := hv.2
  have hs : oneGradientStep m A g k=c+tau • d := rfl
  have hq : xrfcDExecutedImage trial A g k=
      tau⁻¹ • (A k c+tau • A k d-combine Q w) := by
    unfold xrfcDExecutedImage
    rw [oneGradientGradient_succ,hs,hgv,map_add,map_smul]
    congr 1
    change H.gradient+(A k c+tau • A k d)-(H.gradient+combine Q w)=_
    abel
  have he : tau • xrfcDImageError trial A g k=A k c-combine Q w := by
    change tau • (xrfcDExecutedImage trial A g k-A k d)=_
    rw [hq,smul_sub,smul_smul,mul_inv_cancel₀ ht,one_smul]
    abel
  change tau • xrfcDImageError trial A g k=_
  rw [he,hc]
  have hcomb : A k (combine D w)-combine Q w=∑ i : Fin k,w i • (A k (D i)-Q i) := by
    simp only [combine,map_sum,map_smul,smul_sub,Finset.sum_sub_distrib]
  rw [hcomb]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp only [D,Q,xrfcDImageError,_root_.sub_apply]
  abel

end
end krylov.Methods
