import krylov.Correction.DiagonalModelChange
import krylov.Correction.ScenarioExpansion

/-!
Article: main_krylov, thm:C2(c) and apD:lem-model, nonsmooth observed-model replacements.
Use: choose a genuine cubic tube before every actual symmetric source
scenario and every small data-only scalar replacement of the final model.
Source: reuse the actual full modified RFC expansion in the joint finite
source/replacement coordinates; no regularity of a subsequent selector is assumed.
-/

namespace krylov.Correction
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Secant krylov.Envelope
  krylov.Methods krylov.Stability krylov.LinearAlgebra krylov.Variation
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

/-- The actual modified RFC terminal solve has one genuine cubic tube over all original finite symmetric source variables and an independently chosen scalar model change.
Use: plug in a data-only consistency midpoint after proving its size, without assuming that midpoint selector is analytic or differentiable.
Article: main_krylov, thm:C2(c) and apD:lem-model, uniform original-source plus replacement cubic remainder.
Proof: enlarge the true finite source space by one independent real model
coordinate. Original increments, independent query defects and the scalar
model change are analytic coordinate maps on that space. The proved actual
modified canonical theorem gives a genuine joint cubic remainder. Unpack
its actual metric neighborhood once, before every scenario and replacement.
-/
theorem scenario_modified_cubic_tube {k : ℕ}
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1)))
    (hN : k+1≤referenceAtomCount base hb g) (hk : 0<k)
    (D₀ : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) :
    ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ (Θ : symmetricScenarios (k+1) (k+1)) (q : ℝ),
      max ‖Θ‖ |q|≤δ →
      let V := metricRoot base*fullBasisMatrix (referenceModelBasis base g k)
      ‖cgOperator (metricRoot base)⁻¹
          (modifiedTerminalGradient (scenarioProbe base Θ.val) (scenarioCorrection base Θ.val) g k (q • D₀))+
        ‖canonicalCGStep base g k‖ •
          ((staircaseOperator base g (matrixSequenceExtension k Θ.val.1)
            (matrixSequenceExtension (k+1) Θ.val.2 k) (k+1)-cgOperator (inverseCongruence V (q • D₀)))
              (freshDefect base g (matrixSequenceExtension k Θ.val.1) (k+1)))‖≤C*(max ‖Θ‖ |q|)^3 := by
  -- The independent replacement coordinate is an actual extra input to the genuine terminal solve.
  let Y := symmetricScenarios (k+1) (k+1) × ℝ
  let E := fun p : Y => matrixSequenceExtension k p.1.val.1
  let F := fun p : Y => matrixSequenceExtension (k+1) p.1.val.2
  let D := fun p : Y => p.2 • D₀
  have hE (i : ℕ) : AnalyticAt ℝ (fun p : Y => E p i) 0 :=
    (symmetricScenario_increment_analytic (n := k+1) (N := k+1) i).comp (f := fun p : Y => p.1) (x := 0) analyticAt_fst
  have hF (i : ℕ) : AnalyticAt ℝ (fun p : Y => F p i) 0 :=
    (symmetricScenario_correction_analytic (n := k+1) (N := k+1) i).comp (f := fun p : Y => p.1) (x := 0) analyticAt_fst
  have hE0 (i : ℕ) : E 0 i=0 := matrixSequenceExtension_zero k i
  have hF0 (i : ℕ) : F 0 i=0 := matrixSequenceExtension_zero (k+1) i
  have hD : AnalyticAt ℝ D 0 := analyticAt_snd.smul analyticAt_const
  have horder := full_modified_canonical_second_order base hb g hN hk E F hE hF hE0 hF0
    (fun p i => symmetricScenario_increment_symm p.1 i) D hD (zero_smul _ _)
  obtain ⟨C,hC,hbound⟩ := isBigO_iff'.mp horder
  obtain ⟨ε,hε,hεbound⟩ := Metric.eventually_nhds_iff.mp hbound
  refine ⟨ε/2,C,half_pos hε,hC,?_⟩
  intro Θ q hsize
  -- The same actual product-norm ball includes every subsequently chosen, possibly nonsmooth, data selector.
  have hp : dist ((Θ,q) : Y) 0<ε := by
    simpa only [dist_zero_right,Prod.norm_def,Real.norm_eq_abs] using hsize.trans_lt (half_lt_self hε)
  have ht := hεbound hp
  have hAeq : scenarioProbe base Θ.val=canonicalFCPath base (matrixSequenceExtension k Θ.val.1) 1 := rfl
  have hBeq : scenarioCorrection base Θ.val=(fun i => canonicalCorrectionOperator base
      (matrixSequenceExtension k Θ.val.1) (matrixSequenceExtension (k+1) Θ.val.2 i) i) := rfl
  rw [hAeq,hBeq]
  simpa only [E,F,D,Real.norm_of_nonneg (pow_nonneg (norm_nonneg ((Θ,q) : Y)) 3),
    Prod.norm_def,Real.norm_eq_abs] using ht

end
end krylov.Correction
