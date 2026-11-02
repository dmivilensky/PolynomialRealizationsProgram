import krylov.Convergence.ObservableRestart
import krylov.Convergence.WindowMetricExecution

/-!
Article: main_krylov, apG:Dunif, genuine physical RFC correction energy.
Use: identify the actual computed correction, its observed model energy,
and its actual line-energy denominator with the canonical direction-frame
quantities. Source: primal/dual metric covariance and exact nonsingular
rescaling of the newest observed line pair. No correction/output identity
or successful future gate is assumed in these algebraic dictionaries.
-/
namespace krylov.Functions
noncomputable section
open Matrix krylov.Methods krylov.Convergence
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ}
set_option maxHeartbeats 1000000

/-- Every actual latest-model entry is invariant under a genuine
selfadjoint inverse metric coordinate change. -/
theorem pairModel_metric (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric) (s y : Fin p → E) :
    pairModel (fun i=>T (s i)) (fun i=>T.symm (y i))=pairModel s y := by
  ext i j
  exact inverse_symmetric_pairing T hT _ _

/-- The computed coefficients of the actual rectangular observed model
are identical in physical and canonical metric coordinates. -/
theorem modelCoefficients_metric (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric) (s y : Fin p → E) (g : E) :
    modelCoefficients (fun i=>T (s i)) (pairModel (fun i=>T (s i)) (fun i=>T.symm (y i)))
      (T.symm g)=modelCoefficients s (pairModel s y) g := by
  have hc : coordinates (fun i=>T (s i)) (T.symm g)=coordinates s g := by
    funext i
    exact inverse_symmetric_pairing T hT _ _
  simp only [modelCoefficients,pairModel_metric T hT,hc]

/-- Genuine physical model queries transport exactly, for rectangular
windows too and including totalized singular model inverses. -/
theorem modelCorrection_metric (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric) (s y : Fin p → E) (g : E) :
    T (combine s (modelCoefficients s (pairModel s y) g))=
      combine (fun i=>T (s i))
        (modelCoefficients (fun i=>T (s i)) (pairModel (fun i=>T (s i)) (fun i=>T.symm (y i)))
          (T.symm g)) := by
  simp only [modelCoefficients_metric T hT,combine,map_sum,map_smul]

/-- The observed model energy is an actual scalar coordinate invariant. -/
theorem modelEnergy_metric (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric) (s y : Fin p → E) (g : E) :
    let c:=modelCoefficients s (pairModel s y) g
    let c':=modelCoefficients (fun i=>T (s i))
      (pairModel (fun i=>T (s i)) (fun i=>T.symm (y i))) (T.symm g)
    c ⬝ᵥ (pairModel s y*ᵥc)=c' ⬝ᵥ
      (pairModel (fun i=>T (s i)) (fun i=>T.symm (y i))*ᵥc') := by
  dsimp only
  rw [modelCoefficients_metric T hT,pairModel_metric T hT]

/-- A true coefficient solve under a nonsingular column rescaling has
the corresponding original coefficient vector after multiplication by D. -/
theorem modelCoefficients_rescale_mul (s : ι → E) (M : Matrix ι ι ℝ) (D : ι → ℝ)
    (hD : IsUnit (diagonal D).det) (g : E) :
    diagonal D*ᵥmodelCoefficients (rescaleWindow s D) (rescaleModel M D) g=
      modelCoefficients s M g := by
  rw [modelCoefficients,coordinates_rescale,mulVec_neg,mulVec_mulVec,mulVec_mulVec,
    rescaleModel_inverse M D hD]
  rfl

/-- The genuine computed quadratic energy is unchanged by any
nonsingular rescaling of the actual observed model columns. -/
theorem modelEnergy_rescale (s : ι → E) (M : Matrix ι ι ℝ) (D : ι → ℝ)
    (hD : IsUnit (diagonal D).det) (g : E) :
    let c:=modelCoefficients s M g
    let c':=modelCoefficients (rescaleWindow s D) (rescaleModel M D) g
    c' ⬝ᵥ (rescaleModel M D*ᵥc')=c ⬝ᵥ (M*ᵥc) := by
  have he (v : ι → ℝ) : v ⬝ᵥ (rescaleModel M D*ᵥv)=
      (diagonal D*ᵥv) ⬝ᵥ (M*ᵥ(diagonal D*ᵥv)) := by
    simp only [rescaleModel,←mulVec_mulVec,mulVec_diagonal,dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    ring
  dsimp only
  rw [he,modelCoefficients_rescale_mul s M D hD]

/-- The canonical true direction/probe window, with the actual old pairs. -/
def observableRFCMetricSteps (T : E ≃L[ℝ] E) (W : List (E×E)) (d : E) :
    Fin (W.length+1) → E := Fin.cons d (fun i=>T (windowSteps W i))

/-- Actual old observed secants are transformed dually. -/
def observableRFCMetricImages (T : E ≃L[ℝ] E) (W : List (E×E)) (z : E) :
    Fin (W.length+1) → E := Fin.cons z (fun i=>T.symm (windowImages W i))

/-- The actual newest line scalar only rescales one coefficient axis. -/
def observableRFCLineScaling (W : List (E×E)) (α : ℝ) : Fin (W.length+1) → ℝ :=
  Fin.cons α (fun _=>1)

/- The actual nonzero line multiplier is a nonsingular coordinate change. -/
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem observableRFCLineScaling_unit (W : List (E×E)) {α : ℝ} (hα : α≠0) :
    IsUnit (diagonal (observableRFCLineScaling W α)).det := by
  apply isUnit_iff_ne_zero.mpr
  rw [det_diagonal]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  refine Fin.cases ?_ (fun _=>?_) i
  · exact hα
  · exact one_ne_zero

/-- Actual augmented observed line steps and images become the direction
frame with its genuine one-axis line scaling. -/
theorem observableRFCMetric_augmented (T : E ≃L[ℝ] E) (W : List (E×E))
    (s y d z : E) (α : ℝ) (hs : T s=α • d) (hy : T.symm y=α • z) :
    (fun i=>T (windowSteps ((s,y)::W) i))=
        rescaleWindow (observableRFCMetricSteps T W d) (observableRFCLineScaling W α) ∧
    (fun i=>T.symm (windowImages ((s,y)::W) i))=
        rescaleWindow (observableRFCMetricImages T W z) (observableRFCLineScaling W α) := by
  constructor
  · rw [windowSteps_cons]
    funext i
    refine Fin.cases ?_ (fun j=>?_) i
    · exact hs
    · simp only [Fin.cons_succ,observableRFCMetricSteps,observableRFCLineScaling,rescaleWindow,
        Fin.cons_succ,one_smul]
  · rw [windowImages_cons]
    funext i
    refine Fin.cases ?_ (fun j=>?_) i
    · exact hy
    · simp only [Fin.cons_succ,observableRFCMetricImages,observableRFCLineScaling,rescaleWindow,
        Fin.cons_succ,one_smul]

/-- The literal physical RFC correction is the true canonical direction
model solve, with its real line rescaling cancelled exactly. -/
theorem rfcFunctionCorrectionStep_metric (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (B : History E) (d z : E) {α : ℝ} (hα : α≠0)
    (hs : T (rfcFunctionLineStep T f fullMemory r x₀ B)=α • d)
    (hy : T.symm (G (rfcFunctionLinePoint T f fullMemory r x₀ B)-B.gradient)=α • z)
    (hgate : rfcFunctionGate fullMemory B) :
    T (rfcFunctionCorrectionStep T f G fullMemory r x₀ B)=
      combine (observableRFCMetricSteps T (selectedWindow fullMemory B) d)
        (modelCoefficients (observableRFCMetricSteps T (selectedWindow fullMemory B) d)
          (pairModel (observableRFCMetricSteps T (selectedWindow fullMemory B) d)
            (observableRFCMetricImages T (selectedWindow fullMemory B) z))
          (T.symm (G (rfcFunctionLinePoint T f fullMemory r x₀ B)))) := by
  let W:=selectedWindow fullMemory B
  let s:=rfcFunctionLineStep T f fullMemory r x₀ B
  let y:=G (rfcFunctionLinePoint T f fullMemory r x₀ B)-B.gradient
  let g:=G (rfcFunctionLinePoint T f fullMemory r x₀ B)
  have haug := observableRFCMetric_augmented T W s y d z α hs hy
  simp only [rfcFunctionCorrectionStep,ite_eq_left hgate]
  rw [←pairModel_window,modelCorrection_metric T hT,haug.1,haug.2,pairModel_rescale]
  exact modelCorrection_rescale _ _ _ (observableRFCLineScaling_unit W hα) _

/-- The literal observable correction energy equals the true canonical
direction-model quadratic energy, with exactly the same computed solve. -/
theorem observableCorrectionEnergy_metric (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (B : History E) (d z : E) {α : ℝ} (hα : α≠0)
    (hs : T (rfcFunctionLineStep T f fullMemory r x₀ B)=α • d)
    (hy : T.symm (G (rfcFunctionLinePoint T f fullMemory r x₀ B)-B.gradient)=α • z)
    (hgate : rfcFunctionGate fullMemory B) :
    let s:=observableRFCMetricSteps T (selectedWindow fullMemory B) d
    let y:=observableRFCMetricImages T (selectedWindow fullMemory B) z
    let c:=modelCoefficients s (pairModel s y)
      (T.symm (G (rfcFunctionLinePoint T f fullMemory r x₀ B)))
    observableCorrectionEnergy T f G r x₀ B=c ⬝ᵥ (pairModel s y*ᵥc) := by
  let W:=selectedWindow fullMemory B
  let s:=rfcFunctionLineStep T f fullMemory r x₀ B
  let y:=G (rfcFunctionLinePoint T f fullMemory r x₀ B)-B.gradient
  let g:=G (rfcFunctionLinePoint T f fullMemory r x₀ B)
  have haug := observableRFCMetric_augmented T W s y d z α hs hy
  simp only [observableCorrectionEnergy,ite_eq_left hgate,←pairModel_window]
  rw [modelEnergy_metric T hT,haug.1,haug.2,pairModel_rescale]
  exact modelEnergy_rescale _ _ _ (observableRFCLineScaling_unit W hα) _

/-- The actual line-energy denominator is the same scalar in metric
coordinates and acquires exactly the square of the true line multiplier. -/
theorem observableRFC_line_energy_metric (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric) (s y d z : E) (α : ℝ)
    (hs : T s=α • d) (hy : T.symm y=α • z) :
    inner ℝ s y=α^2*inner ℝ d z := by
  rw [←inverse_symmetric_pairing T hT s y,hs,hy,real_inner_smul_left,real_inner_smul_right]
  ring

/-- Empty memory makes the original actual defect gate false. -/
theorem rfcFunctionGate_empty (B : History E)
    (hW : selectedWindow fullMemory B=[]) : ¬rfcFunctionGate fullMemory B := by
  simp only [rfcFunctionGate,hW,ne_eq,not_true_eq_false,false_and,not_false_eq_true]

/-- The real physical correction and observable energy are both zero
on the original empty-memory branch. -/
theorem observableRFC_empty (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (B : History E) (hW : selectedWindow fullMemory B=[]) :
    rfcFunctionCorrectionStep T f G fullMemory r x₀ B=0 ∧
      observableCorrectionEnergy T f G r x₀ B=0 := by
  have hg:=rfcFunctionGate_empty B hW
  constructor
  · simp only [rfcFunctionCorrectionStep,ite_eq_right hg]
  · simp only [observableCorrectionEnergy,ite_eq_right hg]

/-- At a genuine stationary line endpoint, the augmented direction-model
right-hand side is identically zero when there are no old pairs. -/
theorem observableRFCMetricCoefficients_empty (T : E ≃L[ℝ] E) (W : List (E×E))
    (d z g : E) (hW : W=[]) (hline : inner ℝ d g=0) :
    modelCoefficients (observableRFCMetricSteps T W d)
      (pairModel (observableRFCMetricSteps T W d) (observableRFCMetricImages T W z)) g=0 := by
  subst W
  have hc : coordinates (observableRFCMetricSteps T [] d) g=0 := by
    funext i
    refine Fin.cases ?_ (fun j=>Fin.elim0 j) i
    exact hline
  simp only [modelCoefficients,hc,mulVec_zero,neg_zero]

/-- The true computed direction-model correction and energy also vanish
in the empty case; this proves agreement with the actual skipped query. -/
theorem observableRFCMetric_empty (T : E ≃L[ℝ] E) (W : List (E×E))
    (d z g : E) (hW : W=[]) (hline : inner ℝ d g=0) :
    let s:=observableRFCMetricSteps T W d
    let y:=observableRFCMetricImages T W z
    let c:=modelCoefficients s (pairModel s y) g
    combine s c=0 ∧ c ⬝ᵥ (pairModel s y*ᵥc)=0 := by
  dsimp only
  rw [observableRFCMetricCoefficients_empty T W d z g hW hline]
  simp only [combine,Pi.zero_apply,zero_smul,Finset.sum_const_zero,mulVec_zero,dotProduct_zero]
  trivial

end
end krylov.Functions
