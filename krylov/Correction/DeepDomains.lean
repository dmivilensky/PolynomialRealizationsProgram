import krylov.Correction.DeepFamily

/-!
Article: main_krylov, prop:deep, genuine source execution and singular-model certification.
Use: All actual physical search and correction operators of the printed affine family are positive.
Source: original RFC array execution, earlier-package integer checker
soundness, standard real continuity and the intermediate value theorem.
-/

namespace krylov.Correction
noncomputable section
open Matrix Finset krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.LinearAlgebra krylov.Information
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator MatrixOrder

/-- Every actual canonical source probe plus any original-sized symmetric correction is positive definite over the full affine parameter interval and source horizon.
Use: Verify all real source operator domains before the singular-model argument.
Article: main_krylov, prop:deep, actual checked source-family argument.
Proof: The actual accumulated increments cost at most three original budgets and the independent correction costs one. Their true symmetric total deviation has norm strictly below one, so the existing positive-shift theorem proves the actual operator positive. -/
theorem deep_augmented_probe_posDef (s : ℝ) (hs : s∈Set.Icc 0 1) (k : ℕ) (hk : k≤3)
    (F : Matrix (Fin 4) (Fin 4) ℝ) (hF : F.IsSymm) (hFn : ‖F‖≤deepBudget) :
    ((deepCanonicalScenario s).probe k+F).PosDef := by
  -- The actual finite source drift and one independent correction remain strictly within the positive unit metric ball.
  let E := (∑ l∈range k, deepIncrement s l)+F
  have hsum : ‖∑ l∈range k, deepIncrement s l‖≤(k : ℝ)*deepBudget := by
    have he := (norm_sum_le (range k) (deepIncrement s)).trans
      (sum_le_sum (fun l _ => (deepIncrement_budget s hs l).le))
    simpa only [sum_const,card_range,nsmul_eq_mul] using he
  have hsmall : ‖E‖<1 := by
    have hkr : (k : ℝ)≤3 := by exact_mod_cast hk
    have he := (norm_add_le (∑ l∈range k, deepIncrement s l) F).trans (add_le_add hsum hFn)
    have hω := deepBudget_pos
    have hb : 4*deepBudget<1 := by norm_num [deepBudget]
    dsimp only [E]
    nlinarith
  have hsym : E.IsSymm := by
    change ((∑ l∈range k, deepIncrement s l)+F)ᵀ=_
    simp only [transpose_add,transpose_sum,hF.eq]
    congr 1
    apply sum_congr rfl
    intro l _
    exact (deepIncrement_isSymm s l).eq
  have hp := (strict_shifted_posDef E hsym hsmall).2
  change (1+∑ l∈range k, deepIncrement s l+F).PosDef
  convert hp using 1
  simp only [E,add_assoc,one_smul]

/-- Every genuine physical probe in the original four-dimensional affine family is positive definite on its actual finite source horizon.
Use: Establish the real physical search-operator domain uniformly in the original parameter.
Article: main_krylov, prop:deep, actual checked source-family argument.
Proof: The independently proved canonical positive probe transports through the actual nonsingular positive-root form. -/
theorem deepScenario_probe_posDef (s : ℝ) (hs : s∈Set.Icc 0 1) (k : ℕ) (hk : k≤3) :
    ((deepScenario s).probe k).PosDef := by
  have hp := deep_augmented_probe_posDef s hs k hk 0 Matrix.isSymm_zero (by simpa using deepBudget_pos.le)
  rw [add_zero] at hp
  change (((deepCanonicalScenario s).inPhysical (metricRoot deepReference)⁻¹).probe k).PosDef
  rw [Scenario.inPhysical,Scenario.mapForms_probe]
  exact inverseForm_posDef _ _ (Matrix.isUnit_nonsing_inv_det _ (metricRoot_det_unit deepReference deepReference_posDef)) hp

/-- Every actual independent preterminal physical correction operator in the original affine family is positive definite.
Use: Retain genuine positive correction-oracle domains for the source counterexample.
Article: main_krylov, prop:deep, actual checked source-family argument.
Proof: Its actual canonical probe-plus-defect is within four original budgets of the identity. Exact physical form transport preserves the proved positive definiteness. -/
theorem deepScenario_intermediate_posDef (s : ℝ) (hs : s∈Set.Icc 0 1) (k : ℕ) (hk : k<3) :
    ((deepScenario s).intermediate k).PosDef := by
  have hp := deep_augmented_probe_posDef s hs k hk.le (deepCorrection k) (deepCorrection_isSymm k) (deepCorrection_budget k).le
  change (((deepCanonicalScenario s).inPhysical (metricRoot deepReference)⁻¹).intermediate k).PosDef
  rw [Scenario.inPhysical,Scenario.mapForms_intermediate]
  exact inverseForm_posDef _ _ (Matrix.isUnit_nonsing_inv_det _ (metricRoot_det_unit deepReference deepReference_posDef)) hp

/-- The actual physical terminal correction operator of the original affine family is positive definite throughout the whole parameter interval.
Use: Separate the real positive oracle operator from its nearly singular observed correction model.
Article: main_krylov, prop:deep, actual checked source-family argument.
Proof: The genuine canonical terminal probe and original terminal defect satisfy the proved strict four-budget positive-shift bound, and actual inverse-root transport preserves that positivity. -/
theorem deepScenario_last_posDef (s : ℝ) (hs : s∈Set.Icc 0 1) :
    ((deepScenario s).lastOperator 3).PosDef := by
  have hp := deep_augmented_probe_posDef s hs 3 le_rfl deepTerminal deepTerminal_isSymm deepTerminal_budget.le
  change (((deepCanonicalScenario s).inPhysical (metricRoot deepReference)⁻¹).lastOperator 3).PosDef
  rw [Scenario.inPhysical,Scenario.mapForms_lastOperator]
  exact inverseForm_posDef _ _ (Matrix.isUnit_nonsing_inv_det _ (metricRoot_det_unit deepReference deepReference_posDef)) hp

end
end krylov.Correction
