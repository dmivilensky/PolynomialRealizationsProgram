import krylov.Nonlinear.RFCSAveragedBounds
import krylov.Correction.RFCSReferenceTube

/-!
Article: main_krylov, thm:RFCS, genuine nonlinear scaled only-last-probe remainder.
Use: Transfer the original fixed-reference operator estimates to genuine nonlinear gradient requests with their actual local Hessian data.
Source: the proved actual query localization, exact averaged-derivative FTC, genuine compact source tubes and real field homogeneity.
-/

namespace krylov.Nonlinear
noncomputable section
open Set krylov.Methods krylov.Reference krylov.Correction
variable {k : ℕ}

/-- The genuinely localized nonlinear RFC-S terminal gradient has a common scaled quadratic operator remainder with its actual last averaged-Hessian mismatch and the original fixed CG reference step.
Use: Obtain a cubic actual function remainder when the real Hessian deviations and normalized initial-gradient error scale with the cycle size.
Article: main_krylov, thm:RFCS, genuine nonlinear function remainder transfer.
Proof: Derive the actual averaged probe and total-step operators and their true source norm bound from the local Hessians. The complete genuine measured-transcript dictionary identifies the nonlinear output with the source executor. Exact homogeneity multiplies the proved compact fixed-reference quadratic source remainder by the real positive cycle scale.
-/
theorem compact_rfcs_function_remainder (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hN : ∀ g∈K, k+1≤referenceAtomCount base hb g) (hk : 0<k) :
    ∃ δ C : ℝ, 0<δ ∧ 0<C ∧
      ∀ G : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)),
      ∀ H : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)),
      ∀ x₀ : EuclideanSpace ℝ (Fin (k+1)), ∀ h : ℕ → ℝ,
      ∀ S : Set (EuclideanSpace ℝ (Fin (k+1))), Convex ℝ S → ContinuousOn H S →
      (∀ x∈S, HasFDerivAt G (H x) x) → (∀ i<k+1, h i≠0) →
      (∀ i≤k+1, rfcSFunctionPoint fullMemory G x₀ h i∈S) →
      (∀ i<k+1, rfcSFunctionPoint fullMemory G x₀ h i+h i •
        windowDirection (selectedWindow fullMemory (rfcSFunctionRun fullMemory G x₀ h i))
          (rfcSFunctionRun fullMemory G x₀ h i).gradient∈S) →
      ∀ η : ℝ, 0≤η → 2*η≤δ → (∀ x∈S, ‖H x-cgOperator base‖≤η) →
      ∀ ε : ℝ, 0<ε → ∀ g∈K, ‖ε⁻¹ • G x₀-g‖≤2*η →
      ‖G (rfcSFunctionPoint fullMemory G x₀ h (k+1))-
        ε • ((rfcSFunctionSegment fullMemory G H x₀ h k-rfcSFunctionProbeOperator fullMemory G H x₀ h k)
          (referenceStep (cgOperator base) g k))‖≤C*ε*η^2 := by
  obtain ⟨δ,C,hδ,hC,hbound⟩ := compact_rfcs_fixed_reference_quadratic_tube base hb K hK hN hk
  refine ⟨δ,4*C,hδ,by positivity,?_⟩
  intro G H x₀ h S hS hH hG hh hpoint hprobe η hη hηδ hHbound ε hε g hg hinit
  let Ap := rfcSFunctionProbeOperator fullMemory G H x₀ h
  let A := rfcSFunctionSegment fullMemory G H x₀ h
  let Θ := rfcsParametersOfOperators base Ap A
  let v := ε⁻¹ • G x₀-g
  let z := (g+v,Θ)
  have hop := rfcSFunction_averaged_operator_bounds fullMemory G H x₀ h (k+1) S hS hH (cgOperator base) hHbound hpoint hprobe
  have hΘ : ‖Θ‖≤2*η := rfcsParametersOfOperators_norm_le base Ap A hη (fun i hi => (hop i hi).1) (fun i hi => (hop i hi).2)
  have hnorm : ‖(v,Θ)‖≤2*η := norm_prod_le_iff.mpr ⟨hinit,hΘ⟩
  have hestimate := hbound g hg v Θ (hnorm.trans hηδ)
  have hr := rfcSFunctionRun_averaged fullMemory G H x₀ h (k+1) S hS hH hG hh hpoint hprobe
  have hre := rfcsParametersOfOperators_realizes base Ap A (G x₀) (k+1) le_rfl
  have hrun : rfcSFunctionRun fullMemory G x₀ h (k+1)=
      rfcSRun fullMemory (rfcsDirectProbe base z) (rfcsDirectLine base z) (rfcsDirectLine base z) (G x₀) (k+1) := hr.trans hre
  have hgrad := congrArg History.gradient hrun
  rw [rfcSFunctionRun_gradient] at hgrad
  change G (rfcSFunctionPoint fullMemory G x₀ h (k+1))=
    rfcSGradient fullMemory (rfcsDirectProbe base z) (rfcsDirectLine base z) (rfcsDirectLine base z) (G x₀) (k+1) at hgrad
  have hscale : G x₀=ε • (g+v) := by
    have hv : g+v=ε⁻¹ • G x₀ := by dsimp only [v]; abel
    rw [hv,smul_smul,mul_inv_cancel₀ hε.ne',one_smul]
  rw [hscale,(rfcS_scalar fullMemory (rfcsDirectProbe base z) (rfcsDirectLine base z) (rfcsDirectLine base z)
    (g+v) ε hε.ne' (k+1)).1] at hgrad
  change G (rfcSFunctionPoint fullMemory G x₀ h (k+1))=ε • rfcsDirectOutput base z at hgrad
  have hmismatch : rfcsDirectLine base z k-rfcsDirectProbe base z k=A k-Ap k := by
    dsimp only [rfcsDirectProbe]
    rw [sub_sub_cancel]
    simp only [rfcsOperatorAt,dite_eq_left (Nat.lt_succ_self k)]
    rfl
  rw [← hmismatch,hgrad,← smul_sub,norm_smul,Real.norm_of_nonneg hε.le]
  calc
    _ ≤ ε*(C*‖(v,Θ)‖^2) := mul_le_mul_of_nonneg_left hestimate hε.le
    _ ≤ ε*(C*(2*η)^2) := by gcongr
    _ = 4*C*ε*η^2 := by ring

end
end krylov.Nonlinear
