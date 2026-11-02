import krylov.Correction.OriginalUniformModels
import krylov.Correction.GatedScenarioBudget

/-!
Article: main_krylov, thm:UCq, complete original-source observed-model tube.
Use: Apply the genuine ordinary-RFC inverse, measured-gate and normalized-model
bounds to every original finite increment/correction-defect scenario.
Source: proved true finite source-to-operator budget conversion, exact CG
active-atom criterion and arbitrary-scale boundary-inclusive model estimates.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Envelope
open scoped InnerProductSpace Matrix.Norms.L2Operator

/-- Ordinary RFC has uniform genuine active inverse, both measured-gate and original step-normalized model bounds on the complete original finite source class, including zero budgets and arbitrary initial gradients.
Use: Close the full source/scale form of the model part of the ordinary uniform theorem under (N).
Article: main_krylov, thm:UCq.
Proof: Each actual finite increment and correction-defect budget gives the proved dimension-plus-one canonical operator allowance. The original spectral interval gives the true ratio bound, and the actual atom count gives genuine CG activity. Rescale the common radius and constants before all source data, then apply the boundary-inclusive original-scale observed-model theorem to the same ordinary executor.
-/
theorem ordinary_uniform_scenario_models (n : ℕ) (hn : 2≤n) (κ : ℝ) (hκ : 1≤κ) :
    ∃ M₀ ω₀ C : ℝ, 0<M₀ ∧ 0<ω₀ ∧ 0<C ∧
      ∀ (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (μ L : ℝ), 0<μ → L/μ≤κ →
      (∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤L) →
      ∀ (Θ : CanonicalScenario n n) (g : EuclideanSpace ℝ (Fin n)) (ω : ℝ), 0≤ω → ω≤ω₀ →
      referenceAtomCount base hb g=n →
      M₀*ω*‖cgCanonicalError base g 0‖≤‖cgCanonicalError base g (n-2)‖ →
      (∀ i, ‖Θ.1 i‖≤ω) → (∀ i, ‖Θ.2 i‖≤ω) →
      activeObservedModelBounds base (rfcMethod fullMemory 1)
        (scenarioProbe base Θ) (scenarioCorrection base Θ) g n (1/2) C ω := by
  obtain ⟨M,δ,C,hM,hδ,hC,hbound⟩ := ordinary_uniform_original_active_models n hn κ hκ
  let D := (n : ℝ)+1
  have hD : 0<D := by dsimp only [D]; positivity
  refine ⟨M*D,δ/D,C*D,mul_pos hM hD,div_pos hδ hD,mul_pos hC hD,?_⟩
  intro base hb μ L hμ hratio hspec Θ g ω hω he hatoms hN hE hF
  have hspec' i : μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤μ*κ := by
    have hL := (div_le_iff₀ hμ).mp hratio
    exact ⟨(hspec i).1,by nlinarith [(hspec i).2]⟩
  have heδ : D*ω≤δ := by have ht := (le_div_iff₀ hD).mp he; nlinarith only [ht]
  have hpre i (hi : i<n) : CG.gradient (cgOperator base) g i≠0 :=
    cg_nonstagnation base hb g i (by omega)
  have hN' : M*(D*ω)*‖cgCanonicalError base g 0‖≤‖cgCanonicalError base g (n-2)‖ := by
    calc
      _ = (M*D)*ω*‖cgCanonicalError base g 0‖ := by ring
      _ ≤ _ := hN
  have ht := hbound base hb μ hμ hspec' _ _ g (D*ω) (mul_nonneg hD.le hω) heδ hpre hN'
    (fun i hi => (scenario_canonical_operator_budgets base hb Θ hω hE hF i hi).1)
    (fun i hi => (scenario_canonical_operator_budgets base hb Θ hω hE hF i hi).2)
  dsimp only [activeObservedModelBounds] at ht ⊢
  intro k hk hd
  have hm := ht k hk hd
  exact ⟨hm.1,hm.2.1,hm.2.2.1,hm.2.2.2.trans_eq (by ring)⟩

/-- The complete two-dimensional original-source ordinary-RFC model and gate theorem needs no nonstagnation condition, at arbitrary initial scale and including zero budgets.
Use: Supply the model and gate portion of the original n=2 exception.
Article: main_krylov, thm:UCq.
Proof: In dimension two the penultimate nonstagnation error is the initial error itself. Shrink only the uniform source radius by the reciprocal fixed nonstagnation constant; multiplication by the genuine nonnegative initial norm makes (N) automatic.
-/
theorem ordinary_two_dimensional_scenario_models (κ : ℝ) (hκ : 1≤κ) :
    ∃ ω₀ C : ℝ, 0<ω₀ ∧ 0<C ∧
      ∀ (base : Matrix (Fin 2) (Fin 2) ℝ) (hb : base.PosDef) (μ L : ℝ), 0<μ → L/μ≤κ →
      (∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤L) →
      ∀ (Θ : CanonicalScenario 2 2) (g : EuclideanSpace ℝ (Fin 2)) (ω : ℝ), 0≤ω → ω≤ω₀ →
      referenceAtomCount base hb g=2 →
      (∀ i, ‖Θ.1 i‖≤ω) → (∀ i, ‖Θ.2 i‖≤ω) →
      activeObservedModelBounds base (rfcMethod fullMemory 1)
        (scenarioProbe base Θ) (scenarioCorrection base Θ) g 2 (1/2) C ω := by
  obtain ⟨M,δ,C,hM,hδ,hC,hbound⟩ := ordinary_uniform_scenario_models 2 (by omega) κ hκ
  refine ⟨min δ (1/M),C,lt_min hδ (by positivity),hC,?_⟩
  intro base hb μ L hμ hratio hspec Θ g ω hω he hatoms hE hF
  have hMω : M*ω≤1 := by
    have ht := (le_div_iff₀ hM).mp (he.trans (min_le_right _ _))
    nlinarith only [ht]
  apply hbound base hb μ L hμ hratio hspec Θ g ω hω
    (he.trans (min_le_left _ _)) hatoms ?_ hE hF
  simpa only [show (2 : ℕ)-2=0 by omega,one_mul] using
    mul_le_mul_of_nonneg_right hMω (norm_nonneg (cgCanonicalError base g 0))

end
end krylov.Correction
