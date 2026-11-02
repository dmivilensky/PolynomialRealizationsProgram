import krylov.Envelope.TargetedScenarioRegularity
import krylov.Envelope.TargetedGradientJet
import krylov.Envelope.ModelBasisProjectionZero
import krylov.Envelope.ScenarioAxisVariation
import krylov.Envelope.ScenarioPaths
import krylov.Envelope.ScenarioMaximum

set_option autoImplicit false
/-!
Article: main_krylov, apB:prop:consist, actual zero transverse response under reference-only consistency.
Use: prove the genuinely executed reference-targeted one-correction policy has zero true explored variation on every real finite canonical scenario and actual worst value zero.
Source: actual primitive-derived scenario output regularity, genuine target-model derivative cancellation and true full-model/canonical projection geometry.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant Matrix
open scoped Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- The actual reference-targeted terminal method has exactly zero genuine explored first variation on every true source scenario.
Use: The actual reference-targeted terminal method has exactly zero genuine explored first variation on every true source scenario.
Article: main_krylov, apB:prop:consist, actual zero transverse response under reference-only consistency.
Proof: Derive actual finite-scenario differentiability, identify its true source-axis derivative and apply genuine full-model coordinate cancellation and real canonical projection. -/
theorem targeted_scenarioVariation_zero
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (k : ℕ) (hcount : k+1≤referenceAtomCount base hb g) (Θ : CanonicalScenario n (k+1)) :
    scenarioVariation (targetedFinalMethod (k+1) (CG.gradient (cgOperator base) g (k+1))) base g (k+1) Θ=0 := by
  -- Actual finite source paths derive genuine regularity; their chosen reference is the true supplied positive quadratic.
  let target := CG.gradient (cgOperator base) g (k+1)
  let A := fun t : ℝ => scenarioProbe base (t • Θ)
  let B := fun t : ℝ => scenarioCorrection base (t • Θ)
  have hA (j : ℕ) : ContDiffAt ℝ 2 (fun t => A t j) 0 := (scenarioProbe_path_analytic base Θ j).contDiffAt
  have hB (j : ℕ) : ContDiffAt ℝ 2 (fun t => B t j) 0 := (scenarioCorrection_path_analytic base Θ j).contDiffAt
  have hA0 : A 0=fun _ => cgOperator base := by dsimp only [A];rw [zero_smul,scenarioProbe_zero]
  have hB0 : B 0=fun _ => cgOperator base := by dsimp only [B];rw [zero_smul,scenarioCorrection_zero]
  -- The actual target-method output is differentiable without a global consistency hypothesis, so its genuine zero model coordinates determine the true variation.
  have hG := (targeted_scenarioGradient_regular target base hb g k hcount).differentiableAt (by norm_num)
  rw [scenarioVariation_of_differentiable _ base g (k+1) hG Θ]
  apply explored_projection_zero_of_modelBasis (fcMethod fullMemory) fullFC_consistent base hb g k hcount
  intro j
  exact targeted_gradient_deriv_orthogonal A B g k (fun i _ => hA i) (fun i _ => hB i)
    (cgOperator base) hA0 hB0 (cgOperator_positive base hb).1 (cgOperator_positive base hb).2
    (fun i hi => cg_nonstagnation base hb g i (hi.trans_le hcount)) j

/-- The real reference-targeted method has genuine worst transverse variation exactly zero over every actual source budget.
Use: The real reference-targeted method has genuine worst transverse variation exactly zero over every actual source budget.
Article: main_krylov, apB:prop:consist, actual zero transverse response under reference-only consistency.
Proof: Its true variation vanishes on every real finite scenario, including every actual compact maximum witness. -/
theorem targeted_worstTransverse_zero
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (k : ℕ) (hcount : k+1≤referenceAtomCount base hb g) (ω : Fin ((k+1)-1) → ℝ≥0) :
    worstTransverse (targetedFinalMethod (k+1) (CG.gradient (cgOperator base) g (k+1))) base g (k+1) ω=0 := by
  have hmax := (worstTransverse_attained
    (targetedFinalMethod (k+1) (CG.gradient (cgOperator base) g (k+1))) base g (k+1) ω).1
  obtain ⟨Θ,_,hΘ⟩ := hmax
  dsimp only at hΘ
  rw [targeted_scenarioVariation_zero base hb g k hcount Θ,norm_zero] at hΘ
  exact hΘ.symm
end
end krylov.Envelope
