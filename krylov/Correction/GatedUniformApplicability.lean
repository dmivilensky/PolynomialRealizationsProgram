import krylov.Correction.UniformSourceTheorem
import krylov.Correction.GatedScenarioComparison

/-!
Article: main_krylov, thm:UCg(iii), complete original-source applicability.
Use: Choose the nonstagnation constant before the requested spectral threshold,
derive every real passed test and complete ordinary/gated history equality,
and transfer both genuine whole-class terminal inequalities to gated RFC.
Source: the proved original source history theorem and complete ordinary
uniform cubic/model/sharp theorem, including arbitrary scales and zero budgets.
-/

namespace krylov.Correction
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Envelope
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator

/-- The full original ordinary uniform theorem applies to every genuinely defined nonstagnating gated-RFC source cycle, with M₀ and the terminal allowance chosen before γ, and the printed estimates holding on the actual returned gated gradient.
Use: Complete part (iii) of the original uniform spectral-gate theorem together with its actual cubic and all-profile sharp consequences.
Article: main_krylov, thm:UCg(iii), carried by the common thm:UCq inventory row.
Proof: Add the two genuine nonstagnation constants before choosing the threshold, then intersect the positive ordinary and threshold-specific source radii. Actual complete histories and every measured spectral test come from the original source theorem. Their exact terminal gradient equality transfers the complete ordinary cubic expansion and sharp budget-profile bound to the genuine gated executor.
-/
theorem gated_uniform_source_applicability (k : ℕ) (hk : 0<k) (κ : ℝ) (hκ : 1≤κ) :
    ∃ M₀ C : ℝ, 0<M₀ ∧ 0<C ∧
      ∀ γ : ℝ, 0<γ → γ<1 → ∃ ω₀ : ℝ, 0<ω₀ ∧
      ∀ (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef) (μ L : ℝ), 0<μ → L/μ≤κ →
      (∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤L) →
      ∀ (Θ : symmetricScenarios (k+1) (k+1)) (g : EuclideanSpace ℝ (Fin (k+1))) (ω : ℝ),
      0≤ω → ω≤ω₀ → referenceAtomCount base hb g=k+1 →
      M₀*ω*‖cgCanonicalError base g 0‖≤‖cgCanonicalError base g (k+1-2)‖ →
      (∀ i, ‖Θ.val.1 i‖≤ω) → (∀ i, ‖Θ.val.2 i‖≤ω) →
      gatedFullRunDefined γ (scenarioProbe base Θ.val) (scenarioCorrection base Θ.val) g (k+1) →
      let A := scenarioProbe base Θ.val
      let B := scenarioCorrection base Θ.val
      let mg := gatedMethod fullMemory γ (E := EuclideanSpace ℝ (Fin (k+1)))
      let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin (k+1)))
      (∀ j≤k+1, methodRun mg A B g j=methodRun m A B g j) ∧
        actualSpectralGates mg fullMemory A B g (k+1) γ ∧
        ordinarySourceUniformConclusion base Θ g C ω ∧
        (mg.direction (methodRun mg A B g k)≠0 →
          ‖cgOperator (metricRoot base)⁻¹ (probedGradient mg A B g (k+1))+
            ‖cgCanonicalError base g k‖ • staircaseOperator base g
              (matrixSequenceExtension k Θ.val.1) (matrixSequenceExtension (k+1) Θ.val.2 k) (k+1)
              (freshDefect base g (matrixSequenceExtension k Θ.val.1) (k+1))‖≤C*ω^3*‖cgCanonicalError base g 0‖ ∧
          ∀ (w : ℕ → ℝ) (w' : ℝ),
            (∀ i∈range k, ‖matrixSequenceExtension k Θ.val.1 i‖≤w i) →
            ‖matrixSequenceExtension (k+1) Θ.val.2 k‖≤w' →
            ‖cgOperator (metricRoot base)⁻¹ (probedGradient mg A B g (k+1))‖≤
              ‖cgCanonicalError base g k‖*sharpConstant (∑ i∈range k, w i) w'+C*ω^3*‖cgCanonicalError base g 0‖) := by
  obtain ⟨Mo,δo,C,hMo,hδo,hC,hordinary⟩ := ordinary_uniform_source_theorem k hk κ hκ
  obtain ⟨Mg,hMg,hgated⟩ := gated_uniform_nonstagnating_scenario (k+1) (by omega) κ hκ
  refine ⟨Mo+Mg,C,by positivity,hC,?_⟩
  intro γ hγ hγ1
  obtain ⟨δg,hδg,hgate⟩ := hgated γ hγ hγ1
  refine ⟨min δo δg,lt_min hδo hδg,?_⟩
  intro base hb μ L hμ hratio hspec Θ g ω hω he hcount hN hE hF hdefined
  have hNo : Mo*ω*‖cgCanonicalError base g 0‖≤‖cgCanonicalError base g (k+1-2)‖ :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith : Mo≤Mo+Mg) hω) (norm_nonneg _)).trans hN
  have hNg : Mg*ω*‖cgCanonicalError base g 0‖≤‖cgCanonicalError base g (k+1-2)‖ :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith : Mg≤Mo+Mg) hω) (norm_nonneg _)).trans hN
  have ho := hordinary base hb μ L hμ hratio hspec Θ g ω hω (he.trans (min_le_left _ _)) hcount hNo hE hF
  have hg := hgate base hb μ L hμ hratio hspec Θ.val g ω hω (he.trans (min_le_right _ _)) hcount hNg hE hF hdefined
  dsimp only at hg ⊢
  refine ⟨hg.1,hg.2,ho,?_⟩
  intro hd
  have hdir : (gatedMethod fullMemory γ).direction
      (methodRun (gatedMethod fullMemory γ) (scenarioProbe base Θ.val) (scenarioCorrection base Θ.val) g k)=
      (rfcMethod fullMemory 1).direction
        (methodRun (rfcMethod fullMemory 1) (scenarioProbe base Θ.val) (scenarioCorrection base Θ.val) g k) := by
    change windowDirection (selectedWindow fullMemory _) _=windowDirection (selectedWindow fullMemory _) _
    rw [hg.1 k (by omega)]
  rw [hdir] at hd
  have hbnd := ho.2 hd
  have hgrad := congrArg History.gradient (hg.1 (k+1) le_rfl)
  change probedGradient (gatedMethod fullMemory γ) (scenarioProbe base Θ.val) (scenarioCorrection base Θ.val) g (k+1)=
    probedGradient (rfcMethod fullMemory 1) (scenarioProbe base Θ.val) (scenarioCorrection base Θ.val) g (k+1) at hgrad
  rw [hgrad]
  exact hbnd

end
end krylov.Correction
