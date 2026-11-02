import krylov.Correction.ScenarioExpansion

/-!
Article: main_krylov, thm:C and thm:C2(a), profile-independent actual scenario bounds.
Use: obtain a single radius and cubic constant for all original sufficiently
small finite symmetric scenarios at a fixed genuine full reference.
Source: the proved joint finite-scenario cubic expansion and sharp actual-CG
compression bounds. Budget profiles are quantified after choosing the constants.
-/

namespace krylov.Correction
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Variation krylov.Envelope
  krylov.Methods krylov.Secant
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

/-- A single actual finite-scenario tube controls the true cubic remainder for every symmetric perturbation profile.
Use: the radius and constant depend on the reference, and not on a perturbation path or budget profile.
Article: main_krylov, thm:C, original finite-scenario O(ω³) remainder at a fixed reference.
Proof: unpack the genuine joint big-O estimate in the norm of the original
finite source space and take its actual metric neighborhood of zero. -/
theorem scenario_cubic_tube {k : ℕ}
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1)))
    (hN : k+1≤referenceAtomCount base hb g) (hk : 0<k) :
    ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ Θ : symmetricScenarios (k+1) (k+1), ‖Θ‖<δ →
      ‖cgOperator (metricRoot base)⁻¹
        (probedGradient (rfcMethod fullMemory 1) (scenarioProbe base Θ.val)
          (scenarioCorrection base Θ.val) g (k+1))+
        ‖canonicalCGStep base g k‖ • staircaseOperator base g
          (matrixSequenceExtension k Θ.val.1) (matrixSequenceExtension (k+1) Θ.val.2 k) (k+1)
          (freshDefect base g (matrixSequenceExtension k Θ.val.1) (k+1))‖≤C*‖Θ‖^3 := by
  obtain ⟨C,hC,hbound⟩ := isBigO_iff'.mp (scenario_second_order base hb g hN hk)
  obtain ⟨δ,hδ,hδbound⟩ := Metric.eventually_nhds_iff.mp hbound
  refine ⟨δ,C,hδ,hC,?_⟩
  intro Θ hΘ
  have ht := hδbound (by simpa only [dist_zero_right] using hΘ)
  simpa only [Real.norm_of_nonneg (pow_nonneg (norm_nonneg Θ) 3)] using ht

/-- One fixed-reference tube gives the actual RFC sharp spectral upper bound for every original budget profile simultaneously.
Use: budgets, including zero entries, are chosen only after the common radius and cubic constant.
Article: main_krylov, thm:C, the all-profile fixed-reference upper estimate.
Proof: bound the genuine leading staircase/fresh-defect vector by K using
the actual individual canonical budgets. Subtract it from the proved actual
cubic remainder, with its genuine penultimate-error scale. -/
theorem scenario_spectral_upper {k : ℕ}
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1)))
    (hN : k+1≤referenceAtomCount base hb g) (hk : 0<k) :
    ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ Θ : symmetricScenarios (k+1) (k+1), ‖Θ‖<δ →
      ∀ (ω : ℕ → ℝ) (w : ℝ),
      (∀ i∈range k, ‖matrixSequenceExtension k Θ.val.1 i‖≤ω i) →
      ‖matrixSequenceExtension (k+1) Θ.val.2 k‖≤w →
      ‖cgOperator (metricRoot base)⁻¹
        (probedGradient (rfcMethod fullMemory 1) (scenarioProbe base Θ.val)
          (scenarioCorrection base Θ.val) g (k+1))‖≤
        ‖cgCanonicalError base g k‖*sharpConstant (∑ i∈range k, ω i) w+C*‖Θ‖^3 := by
  -- Choose the actual joint remainder tube before seeing any source budget profile.
  obtain ⟨δ,C,hδ,hC,ht⟩ := scenario_cubic_tube base hb g hN hk
  refine ⟨δ,C,hδ,hC,?_⟩
  intro Θ hΘ ω w hω hw
  have hbound := reference_second_order_bound base hb g hN (by omega : 0<k+1)
    (matrixSequenceExtension k Θ.val.1)
    (fun i _ => symmetricScenario_increment_symm Θ i)
    (matrixSequenceExtension (k+1) Θ.val.2 k) ω hω hw
  simp only [Nat.add_sub_cancel] at hbound
  have hc := mul_le_mul_of_nonneg_left hbound (norm_nonneg (canonicalCGStep base g k))
  rw [← Real.norm_of_nonneg (norm_nonneg (canonicalCGStep base g k)),← norm_smul] at hc
  rw [norm_norm] at hc
  have hr := ht Θ hΘ
  have he := norm_sub_le
    (cgOperator (metricRoot base)⁻¹
      (probedGradient (rfcMethod fullMemory 1) (scenarioProbe base Θ.val)
        (scenarioCorrection base Θ.val) g (k+1))+
      ‖canonicalCGStep base g k‖ • staircaseOperator base g
        (matrixSequenceExtension k Θ.val.1) (matrixSequenceExtension (k+1) Θ.val.2 k) (k+1)
        (freshDefect base g (matrixSequenceExtension k Θ.val.1) (k+1)))
    (‖canonicalCGStep base g k‖ • staircaseOperator base g
      (matrixSequenceExtension k Θ.val.1) (matrixSequenceExtension (k+1) Θ.val.2 k) (k+1)
      (freshDefect base g (matrixSequenceExtension k Θ.val.1) (k+1)))
  rw [add_sub_cancel_right] at he
  rw [terminal_step_error_norm base hb g hN]
  exact he.trans ((add_le_add hr hc).trans_eq (add_comm _ _))

end
end krylov.Correction
