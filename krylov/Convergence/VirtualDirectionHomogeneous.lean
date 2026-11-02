import krylov.Methods.HomogeneousTrial
import krylov.Methods.HomogeneousVirtual
import krylov.Methods.DirectionExecution

/-!
Article: main_krylov, lem:U(c,d), thm:V, native direction-basis homogeneity.
Use: derive degree-one homogeneity of the genuine direction replay,
queries, returned gradients and unevaluated output from the primitive
observed degree-zero trial rule. No trajectory covariance is presumed.
Source: induction on the actual finite one-gradient executor and the
proved exact latest-model scalar covariance.
-/
namespace krylov.Convergence
noncomputable section
open krylov.Methods
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual direction replay's virtual block scales with its true
replayed direction/image vectors and actual current gradient. -/
theorem xrfcD_virtualBlock_scalar
    (trial : History E → ℝ) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) (c : ℝ) (hc : c≠0)
    (hd : ∀ i<k,xrfcDExecutedDirection trial A (c • g) i=c • xrfcDExecutedDirection trial A g i)
    (hq : ∀ i<k,xrfcDExecutedImage trial A (c • g) i=c • xrfcDExecutedImage trial A g i)
    (hg : oneGradientGradient (xrfcDMethod fullMemory trial) A (c • g) k=
      c • oneGradientGradient (xrfcDMethod fullMemory trial) A g k) :
    virtualCorrection (xrfcDWindow trial A (c • g) k)
      (oneGradientGradient (xrfcDMethod fullMemory trial) A (c • g) k)=
      c • virtualCorrection (xrfcDWindow trial A g k)
        (oneGradientGradient (xrfcDMethod fullMemory trial) A g k) ∧
    xrfcDVirtualGradient trial A (c • g) k=c • xrfcDVirtualGradient trial A g k ∧
    xrfcDExecutedDirection trial A (c • g) k=c • xrfcDExecutedDirection trial A g k := by
  let D:=fun i : Fin k=>xrfcDExecutedDirection trial A g (k-1-i.val)
  let Y:=fun i : Fin k=>xrfcDExecutedImage trial A g (k-1-i.val)
  have hD : (fun i : Fin k=>xrfcDExecutedDirection trial A (c • g) (k-1-i.val))=fun i=>c • D i :=
    funext fun i=>hd _ (by omega)
  have hY : (fun i : Fin k=>xrfcDExecutedImage trial A (c • g) (k-1-i.val))=fun i=>c • Y i :=
    funext fun i=>hq _ (by omega)
  simp only [oneGradientGradient] at hg ⊢
  have he := xrfcD_virtual_coordinates trial A g k
  have hec := xrfcD_virtual_coordinates trial A (c • g) k
  have hb := virtualBlock_scalar D Y (oneGradientGradient (xrfcDMethod fullMemory trial) A g k) c hc
  simp only [oneGradientGradient] at hb
  have hv : xrfcDVirtualGradient trial A (c • g) k=c • xrfcDVirtualGradient trial A g k := by
    rw [hec.2,he.2]
    rw [hD,hY,hg]
    exact hb.2.1
  refine ⟨?_,hv,?_⟩
  · rw [hec.1,he.1]
    rw [hD,hY,hg]
    exact hb.1
  · rw [xrfcD_direction_coordinates,xrfcD_direction_coordinates,hD,hY,hec.2,he.2]
    rw [hD,hY,hg]
    exact hb.2.2

/-- Primitive homogeneous trials imply actual direction-basis query and
replay homogeneity throughout every finite observed prefix. Article: V2. -/
theorem xrfcD_scalar_prefix
    (trial : History E → ℝ) (ht : ObservedTrialHomogeneous trial)
    (A : ℕ → E →L[ℝ] E) (g : E) (c : ℝ) (hc : 0<c) (N : ℕ) :
    let method:=xrfcDMethod fullMemory trial
    (∀ j≤N,oneGradientGradient method A (c • g) j=c • oneGradientGradient method A g j) ∧
    (∀ i<N,oneGradientStep method A (c • g) i=c • oneGradientStep method A g i) ∧
    (∀ i<N,xrfcDExecutedDirection trial A (c • g) i=c • xrfcDExecutedDirection trial A g i) ∧
      ∀ i<N,xrfcDExecutedImage trial A (c • g) i=c • xrfcDExecutedImage trial A g i := by
  let method:=xrfcDMethod fullMemory trial
  change (∀ j≤N,oneGradientGradient method A (c • g) j=c • oneGradientGradient method A g j) ∧_
  induction N with
  | zero =>
    refine ⟨?_,by intro i hi;omega,by intro i hi;omega,by intro i hi;omega⟩
    intro j hj
    have he : j=0 := by omega
    subst j
    rfl
  | succ k ih =>
    have hv := xrfcD_virtualBlock_scalar trial A g k c hc.ne' ih.2.2.1 ih.2.2.2 (ih.1 k le_rfl)
    simp only [oneGradientGradient] at hv
    have hτ := oneGradient_trial_scalar trial ht method A g k c hc ih.2.1 ih.1
    have hs : oneGradientStep method A (c • g) k=c • oneGradientStep method A g k := by
      change virtualCorrection (xrfcDWindow trial A (c • g) k) _+
        trial _ • xrfcDExecutedDirection trial A (c • g) k=c • _
      rw [hv.1,hv.2.2,hτ,smul_comm,←smul_add]
      rfl
    have hnext : oneGradientGradient method A (c • g) (k+1)=c • oneGradientGradient method A g (k+1) := by
      simp only [oneGradientGradient_succ,ih.1 k le_rfl,hs,map_smul,smul_add]
    have hqnext : xrfcDExecutedImage trial A (c • g) k=c • xrfcDExecutedImage trial A g k := by
      unfold xrfcDExecutedImage
      rw [hτ,hnext,hv.2.1,←smul_sub,smul_comm]
    refine ⟨?_,?_,?_,?_⟩
    · intro j hj
      by_cases he : j=k+1
      · subst j;exact hnext
      · exact ih.1 j (by omega)
    · intro i hi
      by_cases he : i=k
      · subst i;exact hs
      · exact ih.2.1 i (by omega)
    · intro i hi
      by_cases he : i=k
      · subst i;exact hv.2.2
      · exact ih.2.2.1 i (by omega)
    · intro i hi
      by_cases he : i=k
      · subst i;exact hqnext
      · exact ih.2.2.2 i (by omega)

/-- The true native direction-basis output scales under exactly the
original primitive observed-trial homogeneity. Article: V2, thm:V. -/
theorem xrfcD_scalar_output
    (trial : History E → ℝ) (ht : ObservedTrialHomogeneous trial)
    (A : ℕ → E →L[ℝ] E) (B : E →L[ℝ] E) (g : E) (c : ℝ) (hc : 0<c) (N : ℕ) :
    let method:=xrfcDMethod fullMemory trial
    let H:=oneGradientRun method A g N
    let Hc:=oneGradientRun method A (c • g) N
    method.outputDisplacement Hc=c • method.outputDisplacement H ∧
      method.outputGradient B Hc=c • method.outputGradient B H := by
  let method:=xrfcDMethod fullMemory trial
  have hp := xrfcD_scalar_prefix trial ht A g c hc N
  have hv := xrfcD_virtualBlock_scalar trial A g N c hc.ne' hp.2.2.1 hp.2.2.2 (hp.1 N le_rfl)
  simp only [oneGradientGradient] at hv
  have hd : (oneGradientRun method A (c • g) N).displacement=c • (oneGradientRun method A g N).displacement := by
    simp only [oneGradientRun_displacement_sum,Finset.smul_sum]
    exact Finset.sum_congr rfl fun i hi=>hp.2.1 i (Finset.mem_range.mp hi)
  constructor
  · change (oneGradientRun method A (c • g) N).displacement+virtualCorrection (xrfcDWindow trial A (c • g) N) _=c • _
    rw [hd,hv.1,←smul_add]
    rfl
  · change oneGradientGradient method A (c • g) N+B (virtualCorrection (xrfcDWindow trial A (c • g) N) _)=c • _
    rw [hp.1 N le_rfl,hv.1,map_smul,←smul_add]
    rfl

end
end krylov.Convergence
