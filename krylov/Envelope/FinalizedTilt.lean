import krylov.Envelope.FinalizedResidualJets
import krylov.Envelope.ScenarioVariation
import krylov.Envelope.ScenarioPaths

set_option autoImplicit false
/-!
Article: main_krylov, thm:select and apB:lem:mu(a), actual final Galerkin minus-tilt response.
Use: derive the exact genuine transverse response after one real latest-model
correction of any actual smooth source method on every true scenario.
Source: genuine finalized primitive smooth membership, proved actual own-step
residual cancellation and the real raw-method residual/common-tilt splitting.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Matrix
variable {n : ℕ}

/-- The actual finalized smooth method has genuine explored canonical first variation equal to minus the true common tilt on every active source operator path.
Use: The actual finalized smooth method has genuine explored canonical first variation equal to minus the true common tilt on every active source operator path.
Article: main_krylov, thm:select and apB:lem:mu(a), actual final Galerkin minus-tilt response.
Proof: Use the actual finalized primitive smooth class in the real residual/tilt splitting, and substitute the proved genuine zero own-step residual variation. -/
theorem finalized_actual_tilt (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (A B : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hA : ∀ i<N, ContDiffAt ℝ 2 (fun t => A t i) 0)
    (hB : ∀ i<N, ContDiffAt ℝ 2 (fun t => B t i) 0)
    (hA0 : A 0=fun _ => cgOperator base) (hB0 : B 0=fun _ => cgOperator base)
    (hcount : N≤referenceAtomCount base hb g) :
    (exploredFlag base g N).starProjection (cgOperator (metricRoot base)⁻¹
      (deriv (fun t => probedGradient (finalizedMethod M.policy N) (A t) (B t) g N) 0))=
      -commonTilt base g A N := by
  -- Use the genuine primitive smooth wrapper class rather than an assumed smooth output or transverse response.
  let F := finalizedSmoothClass M N
  have hpre (i : ℕ) (hi : i<N) : CG.gradient (cgOperator base) g i≠0 :=
    cg_nonstagnation base hb g i (hi.trans_le hcount)
  have ht := actual_tilt_splitting F.memory F.policy F.consistent F.admissible A B g base hb
    hA0 hB0 N hA hB hcount (F.smooth _ (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 g N hpre)
  have hz : residualVariation base g F.policy A B N=0 :=
    finalized_residualVariation_zero M base g A B N hA hB _ hA0 hB0
      (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 hpre
  rw [hz,zero_sub] at ht
  exact ht

/-- Every actual smooth source method followed by the real final latest-information correction has exactly minus the genuine common tilt on every true finite canonical scenario.
Use: Every actual smooth source method followed by the real final latest-information correction has exactly minus the genuine common tilt on every true finite canonical scenario.
Article: main_krylov, thm:select and apB:lem:mu(a), actual final Galerkin minus-tilt response.
Proof: Derive actual source-axis regularity and true quadratic reference values, identify the genuine scenario derivative, and apply real final-wrapper residual cancellation. -/
theorem finalized_scenario_variation (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hcount : N≤referenceAtomCount base hb g) (Θ : CanonicalScenario n N) :
    scenarioVariation (finalizedMethod M.policy N) base g N Θ=
      -commonTilt base g (canonicalFCPath base (matrixSequenceExtension (N-1) Θ.1)) N := by
  let F := finalizedSmoothClass M N
  let A := fun t : ℝ => scenarioProbe base (t • Θ)
  let B := fun t : ℝ => scenarioCorrection base (t • Θ)
  have hA (i : ℕ) : ContDiffAt ℝ 2 (fun t => A t i) 0 := (scenarioProbe_path_analytic base Θ i).contDiffAt
  have hB (i : ℕ) : ContDiffAt ℝ 2 (fun t => B t i) 0 := (scenarioCorrection_path_analytic base Θ i).contDiffAt
  have hA0 : A 0=fun _ => cgOperator base := by
    dsimp only [A]
    rw [zero_smul,scenarioProbe_zero]
  have hB0 : B 0=fun _ => cgOperator base := by
    dsimp only [B]
    rw [zero_smul,scenarioCorrection_zero]
  -- Identify the genuine finite-scenario axis with the actual canonical operator path before using the real final-wrapper tilt identity.
  have hv := scenarioVariation_actual F base hb g N hcount Θ
  change scenarioVariation (finalizedMethod M.policy N) base g N Θ=
    (exploredFlag base g N).starProjection (cgOperator (metricRoot base)⁻¹
      (deriv (fun t => probedGradient (finalizedMethod M.policy N) (A t) (B t) g N) 0)) at hv
  rw [hv,finalized_actual_tilt M base hb g A B N (fun i _ => hA i) (fun i _ => hB i) hA0 hB0 hcount]
  congr 2
  exact funext (fun t => scenarioProbe_scale base Θ t)
end
end krylov.Envelope
