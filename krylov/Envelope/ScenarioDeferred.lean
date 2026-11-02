import krylov.Envelope.DeferredFreshResidual
import krylov.Envelope.ScenarioVariation
import krylov.Envelope.ScenarioPaths

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(d), actual calibrated DC variation on true source scenarios.
Use: identify the genuine explored first variation of the real calibrated
primitive smooth deferred method for every actual finite source scenario.
Source: proved actual DC fresh residual variation, true source scenario
scaling and the genuine residual/common-tilt splitting.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Matrix
variable {n : ℕ}

/-- The actual calibrated deferred smooth source method has genuine finite-scenario explored variation equal to square-root last energy times the true fresh defect minus the actual common tilt.
Use: The actual calibrated deferred smooth source method has genuine finite-scenario explored variation equal to square-root last energy times the true fresh defect minus the actual common tilt.
Article: main_krylov, apB:lem:mu(d), actual calibrated DC variation on true source scenarios.
Proof: Derive all real finite source paths and primitive smooth domains, identify the true scenario-axis derivative, and substitute the proved actual fresh residual vector in the genuine raw-method tilt splitting. -/
theorem calibratedDeferred_scenario_variation (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hcount : k+1≤referenceAtomCount base hb g)
    (Θ : CanonicalScenario n (k+1)) (hE : ∀ i, (Θ.1 i).IsSymm) :
    let E := matrixSequenceExtension ((k+1)-1) Θ.1
    let m := deferredMethod fullMemory (k+1) (CG.length (cgOperator base) g k)
    scenarioVariation m base g (k+1) Θ=
      Real.sqrt (cgEnergy base g k) • freshDefect base g E (k+1)-commonTilt base g (canonicalFCPath base E) (k+1) := by
  -- Use the genuine finite source extension and actual primitive calibrated deferred source class.
  let E := matrixSequenceExtension ((k+1)-1) Θ.1
  let M := smoothDeferredClass fullMemory (fun _ hk => hk) (k+1) (CG.length (cgOperator base) g k)
    (E := EuclideanSpace ℝ (Fin n))
  let A := canonicalFCPath base E
  let B := fun t : ℝ => scenarioCorrection base (t • Θ)
  have hA (j : ℕ) : ContDiffAt ℝ 2 (fun t => A t j) 0 := (canonicalFCPath_calculus base E j).1.contDiffAt
  have hB (j : ℕ) : ContDiffAt ℝ 2 (fun t => B t j) 0 := (scenarioCorrection_path_analytic base Θ j).contDiffAt
  have hA0 : A 0=fun _ => cgOperator base := canonicalFCPath_zero base E
  have hB0 : B 0=fun _ => cgOperator base := by
    dsimp only [B]
    rw [zero_smul,scenarioCorrection_zero]
  have hEsym (l : ℕ) : (E l).IsSymm := by
    dsimp only [E,matrixSequenceExtension]
    split
    · exact hE _
    · exact Matrix.isSymm_zero
  -- Identify the real source-axis first derivative before using actual residual cancellation and the true common tilt.
  have hv := scenarioVariation_actual M base hb g (k+1) hcount Θ
  have heq : (fun t : ℝ => scenarioGradient M.policy base g (k+1) (t • Θ))=
      fun t => probedGradient M.policy (A t) (B t) g (k+1) := by
    funext t
    unfold scenarioGradient
    rw [scenarioProbe_scale]
  rw [heq] at hv
  have hQ := cgOperator_positive base hb
  have hpre (i : ℕ) (hi : i<k+1) : CG.gradient (cgOperator base) g i≠0 := cg_nonstagnation base hb g i (hi.trans_le hcount)
  have ht := actual_tilt_splitting M.memory M.policy M.consistent M.admissible A B g base hb hA0 hB0 (k+1)
    (fun j _ => hA j) (fun j _ => hB j) hcount (M.smooth _ hQ.1 hQ.2 g (k+1) hpre)
  have hr : residualVariation base g M.policy A B (k+1)=Real.sqrt (cgEnergy base g k) • freshDefect base g E (k+1) :=
    calibratedDeferred_residualVariation base hb g E hEsym B k (fun j _ => hB j) hB0 hcount
  rw [hr] at ht
  change scenarioVariation M.policy base g (k+1) Θ=_
  rw [hv]
  exact ht
end
end krylov.Envelope
