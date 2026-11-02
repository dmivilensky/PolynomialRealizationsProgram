import krylov.Envelope.ScenarioMaximum

set_option autoImplicit false
/-!
Article: main_krylov, thm:select, attained RFC transverse selection value.
Use: identify the actual worst transverse variation of one-correction
full-memory RFC with the genuine attained common-tilt maximum.
Source: real RFC first variations and compact finite scenario budgets.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Matrix Set
open scoped Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- The actual common tilt attains the selection value on the genuine increment budget.
Use: The actual common tilt attains the selection value on the genuine increment budget.
Article: main_krylov, thm:select, attained RFC transverse selection value.
Proof: Identify the continuous tilt map with the actual frozen common tilt in the proved compact maximum. -/
theorem selectionValue_commonTilt (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g)
    (ω : Fin (N-1) → ℝ≥0) :
    IsGreatest ((fun E => ‖commonTilt base g (canonicalFCPath base (matrixSequenceExtension (N-1) E)) N‖) ''
      incrementBudget N ω) (selectionValue base g N ω) := by
  have hmax := selectionValue_attained base g N ω
  have he : (fun E => ‖canonicalTiltLinear base g N E‖)=
      (fun E => ‖commonTilt base g (canonicalFCPath base (matrixSequenceExtension (N-1) E)) N‖) :=
    funext (fun E => congrArg norm (canonicalTiltLinear_apply base hb g N hN hcount E))
  rwa [he] at hmax

/-- One-correction full-memory RFC attains exactly the genuine common-tilt selection value over all admissible increment and correction scenarios.
Use: One-correction full-memory RFC attains exactly the genuine common-tilt selection value over all admissible increment and correction scenarios.
Article: main_krylov, thm:select, attained RFC transverse selection value.
Proof: The actual RFC variation is minus the common tilt and is independent of correction defects. Extend an actual maximizing increment array by zero defects. -/
theorem rfc_selection_value_attained (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g)
    (ω : Fin (N-1) → ℝ≥0) :
    IsGreatest ((fun Θ => ‖scenarioVariation (rfcMethod fullMemory 1) base g N Θ‖) '' scenarioBudget N ω)
      (selectionValue base g N ω) := by
  -- Actual RFC response discards every correction defect; a true increment maximizer therefore also maximizes the complete scenario budget.
  have he (Θ : CanonicalScenario n N) : ‖scenarioVariation (rfcMethod fullMemory 1) base g N Θ‖=‖canonicalTiltLinear base g N Θ.1‖ := by
    rw [rfc_scenario_variation 1 (by norm_num) base hb g N hN hcount,norm_neg,canonicalTiltLinear_apply base hb g N hN hcount]
  obtain ⟨E,hE,hval⟩ := (selectionValue_attained base g N ω).1
  refine ⟨?_,?_⟩
  · refine ⟨(E,0),⟨hE,(scenarioBudget_zero_mem (n := n) ω).2⟩,?_⟩
    change ‖scenarioVariation (rfcMethod fullMemory 1) base g N (E,0)‖=selectionValue base g N ω
    rw [he]
    exact hval
  · rintro r ⟨Θ,hΘ,rfl⟩
    change ‖scenarioVariation (rfcMethod fullMemory 1) base g N Θ‖≤selectionValue base g N ω
    rw [he]
    exact (selectionValue_attained base g N ω).2 ⟨Θ.1,hΘ.1,rfl⟩

/-- The actual worst transverse RFC variation equals the genuine selection value.
Use: The actual worst transverse RFC variation equals the genuine selection value.
Article: main_krylov, thm:select, attained RFC transverse selection value.
Proof: Take the supremum of the attained actual RFC scenario maximum. -/
theorem rfc_worstTransverse_eq_selectionValue (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g)
    (ω : Fin (N-1) → ℝ≥0) :
    worstTransverse (rfcMethod fullMemory 1) base g N ω=selectionValue base g N ω :=
  (rfc_selection_value_attained base hb g N hN hcount ω).csSup_eq
end
end krylov.Envelope
