import krylov.Correction.GatedScenarioBudget

/-!
Article: main_krylov, thm:UCg(i,ii), complete original finite-scenario bounds.
Use: Apply the actual uniform spectral-gated theorem directly to the original
finite canonical increments and independent correction-defect matrices.
Source: proved true operator-cycle estimates and exact source-budget transport.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator

/-- One common radius and constant give both original whole spectral-class gated-RFC bounds for every genuine finite source scenario.
Use: Complete parts (i) and (ii) in the original variables, including arbitrary initial gradients and zero perturbations.
Article: main_krylov, thm:UCg(i,ii).
Proof: Every true source entry obeys its original maximum-norm budget. The proved root-congruence and cumulative-increment estimates derive both canonical operator bounds, so the actual spectral-cycle theorem applies to the same genuine executor and its own last correction-query trace.
-/
theorem gated_uniform_scenario_cycle (n : ℕ) (hn : 2≤n) (κ γ : ℝ)
    (hκ : 1≤κ) (hγ : 0<γ) (hγ1 : γ<1) :
    ∃ ω₀ C : ℝ, 0<ω₀ ∧ 0<C ∧
      ∀ (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (μ L : ℝ), 0<μ → L/μ≤κ →
      (∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤L) →
      ∀ (Θ : krylov.Envelope.CanonicalScenario n n) (g : EuclideanSpace ℝ (Fin n)) (ω : ℝ),
      0≤ω → ω≤ω₀ → gatedFullRunDefined γ (krylov.Envelope.scenarioProbe base Θ)
        (krylov.Envelope.scenarioCorrection base Θ) g n →
      (∀ i, ‖Θ.1 i‖≤ω) → (∀ i, ‖Θ.2 i‖≤ω) →
      let A := krylov.Envelope.scenarioProbe base Θ
      let B := krylov.Envelope.scenarioCorrection base Θ
      let m := gatedMethod fullMemory γ (E := EuclideanSpace ℝ (Fin n))
      let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
      ‖J (probedGradient m A B g n)‖≤C*ω^2*‖J g‖ ∧
        ((probedPhase m A B g (n-1)).trace≠[] →
          ‖J (probedGradient m A B g n)‖≤C*(ω^2*‖J (probedGradient m A B g (n-1))‖+ω^3*‖J g‖)) := by
  obtain ⟨δ,C,hδ,hC,hbound⟩ := gated_uniform_spectral_cycle n hn κ γ hκ hγ hγ1
  refine ⟨δ,C,hδ,hC,?_⟩
  intro base hb μ L hμ hratio hspec Θ g ω hω he hdefined hE hF
  exact hbound base hb μ L hμ hratio hspec _ _ g ω hω he hdefined
    (fun i hi => (scenario_canonical_operator_budgets base hb Θ hω hE hF i hi).1)
    (fun i hi => (scenario_canonical_operator_budgets base hb Θ hω hE hF i hi).2)

end
end krylov.Correction
