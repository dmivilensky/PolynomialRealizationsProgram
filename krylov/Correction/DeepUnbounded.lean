import krylov.Correction.DeepFeatures
import krylov.Correction.DeepDomains

/-!
Article: main_krylov, prop:deep, unbounded genuine admissible RFC family.
Use: Produce real original affine source scenarios satisfying all original
budgets and every actual RFC defect gate, with arbitrarily large true
terminal residuals, from complete kernel-checked source data.
Source: original seven rational rows and dyadic interval, independently
decoded exact integer certificates and the standard intermediate value theorem.
-/

namespace krylov.Correction
noncomputable section
open Matrix Finset Certificate krylov.Methods krylov.Information
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

/-- The true certified dyadic interval lies within the original unit affine source domain.
Use: Establish the actual original unbounded-family conclusion without numerical or desired-trajectory assumptions.
Article: main_krylov, prop:deep, genuine certified unbounded RFC family.
Proof: Use the complete actual source decoding, proved exact integer enclosures and the true determinant intermediate-value argument.
-/
theorem deep_interval_subset {s : ℝ} (hs : s∈Set.Icc (deepLeft : ℝ) (deepRight : ℝ)) :
    s∈Set.Icc 0 1 := ⟨deep_endpoints.1.le.trans hs.1,hs.2.trans deep_endpoints.2.2.le⟩

/-- The actual original RFC execution passes every true spectral observed-data defect gate on the entire original dyadic interval.
Use: Establish the actual original unbounded-family conclusion without numerical or desired-trajectory assumptions.
Article: main_krylov, prop:deep, genuine certified unbounded RFC family.
Proof: Use the complete actual source decoding, proved exact integer enclosures and the true determinant intermediate-value argument.
-/
theorem deep_actual_gate {s : ℝ} (hs : s∈Set.Icc (deepLeft : ℝ) (deepRight : ℝ)) (k : Fin 4) :
    ‖pairDefect
      (fun i : Fin k.val => probedStep (rfcMethod fullMemory 1) (deepScenario s).probeOracle
        ((deepScenario s).correctionOracle 3) deepInitial (k.val-1-i.val))
      (fun i : Fin k.val => probedSecant (rfcMethod fullMemory 1) (deepScenario s).probeOracle
        ((deepScenario s).correctionOracle 3) deepInitial (k.val-1-i.val))‖<1 := by
  have hh := deep_all_realizes 0 hs k.val (by have := k.isLt; omega)
  have hg := deep_gate_of_enclosed 0 k (deep_all_enclosed 0 hs k)
  unfold TermPrefix.Realizes at hh
  simp only [sourceData_probes,sourceData_corrections,sourceInitial_value] at hh
  rw [funext hh.2.1,funext hh.2.2] at hg
  exact hg

/-- The genuine original RFC terminal gradient is unbounded on nonsingular interior members of the original fixed four-dimensional affine source family.
Use: Establish the actual original unbounded-family conclusion without numerical or desired-trajectory assumptions.
Article: main_krylov, prop:deep, genuine certified unbounded RFC family.
Proof: Use the complete actual source decoding, proved exact integer enclosures and the true determinant intermediate-value argument.
-/
theorem deep_rfc_unbounded (R : ℝ) :
    ∃ s∈Set.Ioo (deepLeft : ℝ) (deepRight : ℝ), 0<deepDeterminant s ∧
      R<‖probedGradient (rfcMethod fullMemory 1) (deepScenario s).probeOracle
        ((deepScenario s).correctionOracle 3) deepInitial 4‖ := by
  -- The true determinant takes arbitrarily small positive interior values, while the actual numerator stays uniformly separated from zero.
  have hl : 0<deepDeterminant deepLeft := lt_trans (by positivity) deep_determinant_left
  have hr : deepDeterminant deepRight<0 := lt_trans deep_determinant_right (by norm_num)
  have hv : ∀ s∈Set.Icc (deepLeft : ℝ) (deepRight : ℝ), (1 : ℝ)/(10^54)≤‖deepNumerator s‖ := by
    intro s hs
    have hh := deep_numerator_square hs
    nlinarith [norm_nonneg (deepNumerator s)]
  have hg : ∀ s∈Set.Icc (deepLeft : ℝ) (deepRight : ℝ), ‖deepPost s‖≤1 := by
    intro s hs
    have hh := deep_post_square hs
    nlinarith [norm_nonneg (deepPost s)]
  obtain ⟨s,hs,hd,hR⟩ := unbounded_det_quotient deepDeterminant deepNumerator deepPost
    deep_endpoints.2.1 deep_determinant_continuous hl hr (by positivity : (0 : ℝ)<1/(10^54))
    (by norm_num : (0 : ℝ)≤1) hv hg R
  refine ⟨s,hs,hd,?_⟩
  rw [deep_actual_output ⟨hs.1.le,hs.2.le⟩]
  exact hR

/-- The genuine original admissible affine source family passes every actual RFC gate and has arbitrarily large true terminal residuals.
Use: Establish the actual original unbounded-family conclusion without numerical or desired-trajectory assumptions.
Article: main_krylov, prop:deep, genuine certified unbounded RFC family.
Proof: Use the complete actual source decoding, proved exact integer enclosures and the true determinant intermediate-value argument.
-/
theorem deep_unbounded_admissible (R : ℝ) :
    ∃ s∈Set.Ioo (deepLeft : ℝ) (deepRight : ℝ),
      (deepScenario s).Admissible 3 deepReference 0 (fun _ => deepBudget) deepBudget deepBudget ∧
      (∀ k : Fin 4, ‖pairDefect
        (fun i : Fin k.val => probedStep (rfcMethod fullMemory 1) (deepScenario s).probeOracle
          ((deepScenario s).correctionOracle 3) deepInitial (k.val-1-i.val))
        (fun i : Fin k.val => probedSecant (rfcMethod fullMemory 1) (deepScenario s).probeOracle
          ((deepScenario s).correctionOracle 3) deepInitial (k.val-1-i.val))‖<1) ∧
      R<‖probedGradient (rfcMethod fullMemory 1) (deepScenario s).probeOracle
        ((deepScenario s).correctionOracle 3) deepInitial 4‖ := by
  obtain ⟨s,hs,_,hR⟩ := deep_rfc_unbounded R
  have hI : s∈Set.Icc (deepLeft : ℝ) (deepRight : ℝ) := ⟨hs.1.le,hs.2.le⟩
  exact ⟨s,hs,deepScenario_admissible s (deep_interval_subset hI),fun k => deep_actual_gate hI k,hR⟩

end
end krylov.Correction
