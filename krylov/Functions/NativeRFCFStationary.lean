import krylov.Functions.NativeRFCF

/-!
Article: main_krylov, prop:Fcycle(ii), exact terminated native cycles.
Use: include zero-error cycles in the genuine restarted RFC-F conclusion.
Source: the actual chord executor and zero observed model right-hand side.
Neither nonzero directions nor a nonsingular model is required.
-/
namespace krylov.Functions
noncomputable section
open krylov.Methods krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A true searched chord in the zero direction returns its starting point,
including the totalized branch. Article: main_krylov, prop:Fcycle(ii). -/
theorem localExactPoint_zero_direction (f : E → ℝ) (x : E) (r : ℝ) :
    localExactPoint f x 0 r=x := by
  classical
  unfold localExactPoint
  split
  · obtain ⟨t,ht⟩ := (Classical.choose_spec (‹∃! y, IsChordMinimum f x 0 r y›).exists).2.1
    simpa only [smul_zero,add_zero] using ht
  · rfl

/-- A real stationary ordinary-RFC record has no movement and returns the
true stationary gradient through either actual gate. Article: main_krylov, prop:Fcycle(ii). -/
theorem rfcFunctionRecord_stationary (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (memory : ℕ → ℕ) (r : ℝ) (x₀ : E) (H : History E)
    (hG : G x₀=0) (hg : H.gradient=0) (hs : H.displacement=0) :
    (rfcFunctionRecord T f G memory r x₀ H).step=0 ∧
      (rfcFunctionRecord T f G memory r x₀ H).gradient=0 := by
  have hd : rfcFunctionDirection memory H=0 := by rw [rfcFunctionDirection,hg,windowDirection_zero]
  have hy : rfcFunctionLinePoint T f memory r x₀ H=x₀ := by
    rw [rfcFunctionLinePoint,hs,add_zero,hd,metricLocalExactPoint,map_zero,
      localExactPoint_zero_direction,T.symm_apply_apply]
  have hstep : rfcFunctionLineStep T f memory r x₀ H=0 := by
    rw [rfcFunctionLineStep,hy,hs,add_zero,sub_self]
  have hc : rfcFunctionCorrectionStep T f G memory r x₀ H=0 := by
    unfold rfcFunctionCorrectionStep
    dsimp only
    rw [hy,hG]
    split
    · rw [modelCoefficients_zero _ _ _ (by ext i; simp only [coordinates,inner_zero_right,Pi.zero_apply])]
      simp only [combine,Pi.zero_apply,zero_smul,Finset.sum_const_zero]
    · rfl
  simp only [rfcFunctionRecord,hstep,hc,hy,hG,add_zero,and_self]

/-- Every real stationary RFC prefix retains zero actual movement and true
zero gradient. Article: main_krylov, prop:Fcycle(ii). -/
theorem rfcFunctionRun_stationary (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (memory : ℕ → ℕ) (r : ℝ) (x₀ : E) (hG : G x₀=0) (N : ℕ) :
    (rfcFunctionRun T f G memory r x₀ N).gradient=0 ∧
      (rfcFunctionRun T f G memory r x₀ N).displacement=0 := by
  induction N with
  | zero => exact ⟨hG,rfl⟩
  | succ i ih =>
    have hr := rfcFunctionRecord_stationary T f G memory r x₀
      (rfcFunctionRun T f G memory r x₀ i) hG ih.1 ih.2
    constructor
    · change (rfcFunctionRecord T f G memory r x₀ (rfcFunctionRun T f G memory r x₀ i)).gradient=0
      exact hr.2
    · change (rfcFunctionRecord T f G memory r x₀ (rfcFunctionRun T f G memory r x₀ i)).step+
        (rfcFunctionRun T f G memory r x₀ i).displacement=0
      rw [hr.1,ih.2,add_zero]

/-- The actual last value-informed solve fixes a stationary point exactly.
Article: main_krylov, prop:Fcycle(ii), including all terminated restart tails. -/
theorem rfcFPoint_stationary (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (hG : G x₀=0) (k : ℕ) : rfcFPoint T f G r x₀ k=x₀ := by
  have hp := rfcFunctionRun_stationary T f G fullMemory r x₀ hG k
  have hd : rfcFunctionDirection fullMemory (rfcFunctionRun T f G fullMemory r x₀ k)=0 := by
    rw [rfcFunctionDirection,hp.1,windowDirection_zero]
  have ha : rfcFAnchor T f G r x₀ k=x₀ := by
    rw [rfcFAnchor,rfcFunctionLinePoint,hp.2,add_zero,hd,metricLocalExactPoint,map_zero,
      localExactPoint_zero_direction,T.symm_apply_apply]
  have hc : rfcFCorrectionStep T f G r x₀ k=0 := by
    unfold rfcFCorrectionStep
    split
    · rw [ha,hG,modelCoefficients_zero _ _ _ (by ext i; simp only [coordinates,inner_zero_right,Pi.zero_apply])]
      simp only [combine,Pi.zero_apply,zero_smul,Finset.sum_const_zero]
    · rfl
  rw [rfcFPoint,ha,hc,add_zero]

end
end krylov.Functions
