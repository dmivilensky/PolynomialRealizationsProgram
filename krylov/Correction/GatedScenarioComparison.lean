import krylov.Correction.GatedOriginalComparison
import krylov.Correction.GatedScenarioBudget

/-!
Article: main_krylov, thm:UCq and thm:UCg(iii), original observed source coordinates.
Use: Transport actual uniform method conclusions and terminal model algebra
through the genuine finite source and chronological observation dictionary.
Source: proved true source-budget congruence, original active CG reference
geometry and exact finite latest-information model identities.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Envelope
open scoped InnerProductSpace Matrix.Norms.L2Operator

/-- The original full finite source class has one nonstagnation constant before every gate threshold, with exact ordinary/gated history equality and every true spectral test passed, including zero budgets and arbitrary actual initial data.
Use: Apply the original uniform theory to the same actual method and observed source data.
Article: main_krylov, thm:UCq and thm:UCg(iii).
Proof: Multiply the proved original operator nonstagnation constant by the dimension-plus-one source allowance, and divide its genuine common radius by the same factor. Actual finite increment and correction-defect entry budgets derive both canonical operator bounds. The original spectral interval gives the true condition-ratio bound and the full source atom count gives genuine CG nonstagnation. Apply the complete original-scale boundary-inclusive history and gate theorem to the same actual source executor.
-/
theorem gated_uniform_nonstagnating_scenario (n : ℕ) (hn : 2≤n) (κ : ℝ) (hκ : 1≤κ) :
    ∃ M₀ : ℝ, 0<M₀ ∧
      ∀ γ : ℝ, 0<γ → γ<1 → ∃ ω₀ : ℝ, 0<ω₀ ∧
      ∀ (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (μ L : ℝ), 0<μ → L/μ≤κ →
      (∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤L) →
      ∀ (Θ : CanonicalScenario n n) (g : EuclideanSpace ℝ (Fin n)) (ω : ℝ), 0≤ω → ω≤ω₀ →
      referenceAtomCount base hb g=n →
      M₀*ω*‖cgCanonicalError base g 0‖≤‖cgCanonicalError base g (n-2)‖ →
      (∀ i, ‖Θ.1 i‖≤ω) → (∀ i, ‖Θ.2 i‖≤ω) →
      gatedFullRunDefined γ (scenarioProbe base Θ) (scenarioCorrection base Θ) g n →
      let A := scenarioProbe base Θ
      let B := scenarioCorrection base Θ
      (∀ k≤n, methodRun (gatedMethod fullMemory γ) A B g k=methodRun (rfcMethod fullMemory 1) A B g k) ∧
        actualSpectralGates (gatedMethod fullMemory γ) fullMemory A B g n γ := by
  obtain ⟨M,hM,hbound⟩ := gated_uniform_nonstagnating_history_nonnegative n hn κ hκ
  let D := (n : ℝ)+1
  have hD : 0<D := by dsimp only [D]; positivity
  refine ⟨M*D,mul_pos hM hD,?_⟩
  intro γ hγ hγ1
  obtain ⟨δ,hδ,hcycle⟩ := hbound γ hγ hγ1
  refine ⟨δ/D,div_pos hδ hD,?_⟩
  intro base hb μ L hμ hratio hspec Θ g ω hω he hatoms hN hE hF hdefined
  have hspec' i : μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤μ*κ := by
    have hL := (div_le_iff₀ hμ).mp hratio
    exact ⟨(hspec i).1,by nlinarith [(hspec i).2]⟩
  have hε : 0≤D*ω := mul_nonneg hD.le hω
  have heδ : D*ω≤δ := by have ht := (le_div_iff₀ hD).mp he; nlinarith only [ht]
  have hpre i (hi : i<n) : CG.gradient (cgOperator base) g i≠0 :=
    cg_nonstagnation base hb g i (by omega)
  have hN' : M*(D*ω)*‖cgCanonicalError base g 0‖≤‖cgCanonicalError base g (n-2)‖ := by
    calc
      _ = (M*D)*ω*‖cgCanonicalError base g 0‖ := by ring
      _ ≤ _ := hN
  exact hcycle base hb μ hμ hspec' _ _ g (D*ω) hε heδ hpre hN'
    (fun i hi => (scenario_canonical_operator_budgets base hb Θ hω hE hF i hi).1)
    (fun i hi => (scenario_canonical_operator_budgets base hb Θ hω hE hF i hi).2) hdefined

end
end krylov.Correction
