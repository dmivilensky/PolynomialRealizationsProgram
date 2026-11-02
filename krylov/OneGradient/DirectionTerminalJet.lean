import krylov.OneGradient.DirectionImageRecurrence
import krylov.Envelope.ModelCorrectionJet
import krylov.Correction.FullReconstruction
import krylov.Stability.ObliqueResponse
set_option autoImplicit false
/-!
Article: main_krylov, thm:I, actual terminal direction-basis native output jet.
Use: derive the true semantic output derivative from original native replay
coefficients and its newest image, before unrolling the image-error recurrence.
Source: genuine native projected correction first jet, real sparse reference
weights, actual full-atom CG termination and true full-basis pairing uniqueness.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability krylov.Envelope krylov.Correction
open scoped BigOperators InnerProductSpace
variable {n : ℕ}

/-- The actual original full-memory direction-basis semantic output has its
true newest-image first derivative on arbitrary primitive C1 operator paths.
Use: no output jet, CG response or replay-image correctness on varying data
is assumed in the source's terminal variation calculation.
Article: main_krylov, thm:I, ghat_n'=rho_(n-1)(DeltaA_(n-1)d_(n-1)^0-iota_(n-1)').
Proof: primitive replay calculus gives every actual finite solve and output
jet. The genuine native normal equation differentiates with frozen reference
coefficients; their true newest-coordinate sparsity leaves the actual last
model-error column. Zero reference drift cancels direction derivatives, and
true full-basis pairing uniqueness reconstructs the real physical output jet. -/
theorem xrfcD_terminal_output_first_jet
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hc : referenceAtomCount base hb g=n) (hn : 0<n)
    (A : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : ∀ k,ContDiffAt ℝ 1 (fun t => A t k) 0) (hA0 : A 0=fun _ => cgOperator base)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0)
    (hT : ∀ k<n,ContDiffAt ℝ 1 (trialCoordinate trial k)
      (oneGradientData (xrfcDMethod fullMemory trial) (fun _ => cgOperator base) g k)) :
    let m := xrfcDMethod fullMemory trial
    deriv (fun t => m.outputGradient (A t n) (oneGradientRun m (A t) g n)) 0=
      (CG.length (cgOperator base) g (n-1)-
        trial (oneGradientRun m (fun _ => cgOperator base) g (n-1))) •
        ((deriv (fun t => A t n) 0-deriv (fun t => A t (n-1)) 0)
          (CG.direction (cgOperator base) g (n-1))-
          deriv (fun t => xrfcDImageError trial (A t) g (n-1)) 0) := by
  let : NeZero n := ⟨by omega⟩
  let Q := cgOperator base
  let m := xrfcDMethod fullMemory trial
  let D := fun t (i : Fin n) => xrfcDExecutedDirection trial (A t) g (n-1-i.val)
  let Y := fun t (i : Fin n) => xrfcDExecutedImage trial (A t) g (n-1-i.val)
  let M := fun t => pairModel (D t) (Y t)
  let G := fun t => oneGradientGradient m (A t) g n
  let out := fun t => m.outputGradient (A t n) (oneGradientRun m (A t) g n)
  let rho := CG.length Q g (n-1)-trial (oneGradientRun m (fun _ => Q) g (n-1))
  let v := (deriv (fun t => A t n) 0-deriv (fun t => A t (n-1)) 0)
      (CG.direction Q g (n-1))-deriv (fun t => xrfcDImageError trial (A t) g (n-1)) 0
  have hp := cgOperator_positive base hb
  have hpre (i : ℕ) (hi : i<n) : CG.gradient Q g i≠0 := cg_nonstagnation base hb g i (by rw [hc];exact hi)
  have hcharts : ∀ k<n,ContDiffAt ℝ 1 (trialCoordinate trial k) (oneGradientData m (A 0) g k) := by
    rw [hA0]
    exact hT
  have hreg := quadraticXRFCD_prefix_contDiffAt trial A (fun _ => g) 0 hA contDiffAt_const Q hA0 hp.1 hp.2 n hpre ht hcharts
  have hD (i : Fin n) : ContDiffAt ℝ 1 (fun t => D t i) 0 := hreg.2.2.1 _ (by omega)
  have hY (i : Fin n) : ContDiffAt ℝ 1 (fun t => Y t i) 0 := hreg.2.2.2 _ (by omega)
  have hM (i j : Fin n) : ContDiffAt ℝ 1 (fun t => M t i j) 0 :=
    (hD (max i j)).inner ℝ (hY (min i j))
  have hout := (quadraticXRFCD_output_contDiffAt trial A (fun t => A t n) (fun _ => g) 0 hA (hA n)
    contDiffAt_const Q hA0 hp.1 hp.2 n hpre ht hcharts).2
  have hout0 : out 0=0 := by
    dsimp only [out]
    rw [hA0]
    have hterm := (xrfcD_terminates base hb g fullMemory trial (fun _ _ hi => hi)
      (by rw [hc];exact ht)).2.1
    rw [hc] at hterm
    exact hterm
  have hdom : (M 0).det≠0 := by
    dsimp only [M,D,Y]
    rw [hA0]
    exact (xrfcD_full_array_domains trial Q hp.1 hp.2 g n hpre ht n le_rfl).2
  have hY0 : Y 0=fun i => Q (D 0 i) := by
    funext i
    dsimp only [Y,D]
    rw [hA0,xrfcD_executed_image_reference trial Q hp.1 hp.2 g n hpre ht _ (by omega),
      xrfcD_executed_direction_reference trial Q hp.1 hp.2 g n hpre ht _ (by omega)]
  have hmodelQ : correctionCompression (D 0) Q=M 0 := by
    change correctionCompression (D 0) Q=pairModel (D 0) (Y 0)
    rw [hY0,pairModel_quadratic (D 0) Q hp.1]
  have hmodel : correctionCompression (D 0) (A 0 n)=M 0 := by
    rw [show A 0 n=Q by rw [hA0]]
    exact hmodelQ
  have hw0 : modelCoefficients (D 0) (M 0) (G 0)=fun i : Fin n => if i=0 then rho else 0 := by
    change xrfcDArrayCoefficients trial (A 0) g n=_
    rw [hA0]
    simpa only [Fin.ext_iff,Fin.val_zero] using
      xrfcD_reference_coefficients_at trial Q hp.1 hp.2 g n hpre ht n le_rfl hn
  have hOut (t : ℝ) : out t=G t+A t n (combine (D t) (modelCoefficients (D t) (M t) (G t))) := by
    change G t+A t n (virtualCorrection (xrfcDWindow trial (A t) g n) (G t))=_
    have hcorr : virtualCorrection (xrfcDWindow trial (A t) g n) (G t)=
      combine (D t) (modelCoefficients (D t) (M t) (G t)) :=
        (xrfcD_virtual_coordinates trial (A t) g n).1
    rw [hcorr]
  let W := fun t => (A t n-A t (n-1)) (xrfcDExecutedDirection trial (A t) g (n-1))-
    xrfcDImageError trial (A t) g (n-1)
  have hI : ContDiffAt ℝ 1 (fun t => xrfcDImageError trial (A t) g (n-1)) 0 :=
    (hreg.2.2.2 _ (by omega)).sub ((hA _).clm_apply (hreg.2.2.1 _ (by omega)))
  have hW0 : W 0=0 := by
    dsimp only [W,xrfcDImageError]
    rw [hA0,xrfcD_executed_image_reference trial Q hp.1 hp.2 g n hpre ht _ (by omega),
      xrfcD_executed_direction_reference trial Q hp.1 hp.2 g n hpre ht _ (by omega)]
    simp only [Q,sub_self,_root_.zero_apply]
  have hWjet : HasDerivAt W v 0 := by
    have h := ((hA n).differentiableAt (by norm_num)).hasDerivAt.fun_sub
      ((hA (n-1)).differentiableAt (by norm_num)).hasDerivAt
    have he := (h.clm_apply ((hreg.2.2.1 (n-1) (by omega)).differentiableAt (by norm_num)).hasDerivAt).fun_sub
      (hI.differentiableAt (by norm_num)).hasDerivAt
    change HasDerivAt W _ 0 at he
    have href : xrfcDExecutedDirection trial (fun _ => cgOperator base) g (n-1)=
        CG.direction Q g (n-1) :=
      xrfcD_executed_direction_reference trial (cgOperator base) hp.1 hp.2 g n hpre ht (n-1) (by omega)
    simpa only [hA0,sub_self,_root_.zero_apply,add_zero,href] using he
  have hunit : IsUnit (fullBasisMatrix (D 0)).det :=
    fullBasisMatrix_unit _ (compression_unit_independent (D 0) Q
      (isUnit_iff_ne_zero.mpr (by rw [hmodelQ];exact hdom)))
  apply column_inner_ext (fullBasisMatrix (D 0)) hunit
  intro i
  change inner ℝ (D 0 i) (deriv out 0)=inner ℝ (D 0 i) (rho • v)
  have hleft := ((hD i).differentiableAt (by norm_num)).hasDerivAt.inner ℝ
    (hout.differentiableAt (by norm_num)).hasDerivAt
  have hleft' : deriv (fun t => inner ℝ (D t i) (out t)) 0=inner ℝ (D 0 i) (deriv out 0) := by
    have hh : deriv (fun t => inner ℝ (D t i) (out t)) 0=
        inner ℝ (D 0 i) (deriv out 0)+inner ℝ (deriv (fun t => D t i) 0) (out 0) := hleft.deriv
    simpa only [hout0,inner_zero_right,add_zero] using hh
  have h := modelCorrection_projected_first_jet D M (fun t => A t n) G hD hM (hA n) (hreg.1 n le_rfl) hdom hmodel i
  simp_rw [← hOut] at h
  rw [hleft',hw0] at h
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at h
  have hentry : (fun t => (correctionCompression (D t) (A t n)-M t) i 0)=fun t => inner ℝ (D t i) (W t) := by
    funext t
    change inner ℝ (D t i) (A t n (D t 0))-inner ℝ (D t (max i 0)) (Y t (min i 0))=_
    rw [max_eq_left (Fin.zero_le i),min_eq_right (Fin.zero_le i),← inner_sub_right]
    congr 1
    dsimp only [W,D,Y,xrfcDImageError,Fin.val_zero,Nat.sub_zero]
    simp only [_root_.sub_apply]
    abel
  have hentryjet := ((hD i).differentiableAt (by norm_num)).hasDerivAt.inner ℝ hWjet
  have hentryder : deriv (fun t => (correctionCompression (D t) (A t n)-M t) i 0) 0=
      inner ℝ (D 0 i) v := by
    rw [hentry]
    simpa only [hW0,inner_zero_right,add_zero] using hentryjet.deriv
  rw [hentryder] at h
  rw [h,real_inner_smul_right,mul_comm]

end
end krylov.OneGradient
