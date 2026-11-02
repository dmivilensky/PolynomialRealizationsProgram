import krylov.Nonlinear.RFCSFunction

/-!
Article: main_krylov, thm:RFCS, actual stationary nonlinear cycles.
Use: Include exact stationary and zero-error cycles in the real nonlinear
finite-probe executor and its restarted consequences.
Source: the actual observed direction/zero-model-right-hand-side identities;
all genuine searches and physical corrections are zero in both actual gates.
-/

namespace krylov.Nonlinear
noncomputable section
open krylov.Methods krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A genuine stationary current gradient with zero accumulated movement makes the actual next nonlinear RFC-S total step and returned gradient zero, through either real gate branch.
Use: Handle actual terminated cycles without nonzero-search or inverse-domain premises.
Article: main_krylov, thm:RFCS, true stationary nonlinear execution.
Proof: The true data-only direction is zero. Its actual finite difference and predicted search vanish; the real model right-hand side and physical correction are zero, so the genuine evaluation remains stationary.
-/
theorem rfcSFunctionRecord_stationary (memory : ℕ → ℕ) (G : E → E) (x₀ : E) (h : ℝ) (H : History E)
    (hG : G x₀=0) (hg : H.gradient=0) (hs : H.displacement=0) :
    (rfcSFunctionRecord memory G x₀ h H).step=0 ∧ (rfcSFunctionRecord memory G x₀ h H).gradient=0 := by
  have hcoeff (W : List (E × E)) : modelCoefficients (windowSteps W) (windowModel W) (0 : E)=0 :=
    modelCoefficients_zero _ _ _ (by ext i; simp only [coordinates,inner_zero_right,Pi.zero_apply])
  unfold rfcSFunctionRecord
  dsimp only
  simp only [hs,add_zero,hg,windowDirection_zero,smul_zero,hG,sub_zero,lineLength,inner_zero_left,
    neg_zero,zero_div,searchedGradient]
  split
  · rw [hcoeff]
    simp only [combine,Pi.zero_apply,zero_smul,Finset.sum_const_zero,add_zero,hG,and_self]
  · exact ⟨rfl,rfl⟩

/-- Every genuine nonlinear RFC-S prefix at a stationary initial point has zero true current gradient and zero actual accumulated movement.
Use: Cover all stopped tails and zero-error cycle cases of the real function executor.
Article: main_krylov, thm:RFCS, true stationary nonlinear execution.
Proof: Induct over actual records using the proved genuine zero-step/gradient identity, including both true gate branches.
-/
theorem rfcSFunctionRun_stationary (memory : ℕ → ℕ) (G : E → E) (x₀ : E) (h : ℕ → ℝ)
    (hG : G x₀=0) (N : ℕ) :
    (rfcSFunctionRun memory G x₀ h N).gradient=0 ∧ (rfcSFunctionRun memory G x₀ h N).displacement=0 := by
  induction N with
  | zero => exact ⟨hG,rfl⟩
  | succ i ih =>
    have hr := rfcSFunctionRecord_stationary memory G x₀ (h i) (rfcSFunctionRun memory G x₀ h i) hG ih.1 ih.2
    constructor
    · change (rfcSFunctionRecord memory G x₀ (h i) (rfcSFunctionRun memory G x₀ h i)).gradient=0
      exact hr.2
    · change (rfcSFunctionRecord memory G x₀ (h i) (rfcSFunctionRun memory G x₀ h i)).step+
        (rfcSFunctionRun memory G x₀ h i).displacement=0
      rw [hr.1,ih.2,add_zero]

/-- Every real finite-probe RFC-S prefix fixes a genuinely stationary initial point exactly.
Use: Preserve the original error zero after actual finite termination in restarted cycles.
Article: main_krylov, thm:RFCS, true stationary nonlinear execution.
Proof: Read the exact actual zero accumulated movement from the proved stationary run invariant.
-/
theorem rfcSFunctionPoint_stationary (memory : ℕ → ℕ) (G : E → E) (x₀ : E) (h : ℕ → ℝ)
    (hG : G x₀=0) (N : ℕ) : rfcSFunctionPoint memory G x₀ h N=x₀ := by
  rw [rfcSFunctionPoint,(rfcSFunctionRun_stationary memory G x₀ h hG N).2,add_zero]

end
end krylov.Nonlinear
