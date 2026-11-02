import krylov.Envelope.CorrectionFreeInvisible
import krylov.Envelope.ScenarioDeferred

set_option autoImplicit false
/-!
Article: Lemma B.17 [apB:lem:mu] of krylov.tex.
Use: close the printed invisible-scenario residual identity for every actual correction-free primitive smooth source method.
Source: actual invisible-fibre scenario variation, genuine primitive-derived residual/common-tilt splitting and real source path regularity.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Matrix
variable {n : ℕ}

/-- On every actual invisible source scenario the genuine own-step residual variation of every correction-free smooth method is exactly the printed fresh defect times square-root final energy.
Use: On every actual invisible source scenario the genuine own-step residual variation of every correction-free smooth method is exactly the printed fresh defect times square-root final energy.
Article: main_krylov, apB:lem:mu(d), the genuine correction-free fresh own-step residual.
Proof: Derive actual source path domains, identify the true scenario-axis derivative and cancel the real common tilt in the proved actual splitting. -/
theorem correctionFree_invisible_residualVariation (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (hfree : Methods.CorrectionFree M.policy)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (k : ℕ) (hk : 0<k) (hcount : k+1≤referenceAtomCount base hb g) (Θ : CanonicalScenario n (k+1))
    (hE : ∀ i,(Θ.1 i).IsSymm)
    (hInv : InvisibleIncrements base g (matrixSequenceExtension ((k+1)-1) Θ.1) (k+1)) :
    let E := matrixSequenceExtension ((k+1)-1) Θ.1
    residualVariation base g M.policy (canonicalFCPath base E)
      (fun t : ℝ => scenarioCorrection base (t • Θ)) (k+1)=
      Real.sqrt (cgEnergy base g k) • freshDefect base g E (k+1) := by
  -- Genuine primitive source paths derive all actual regularity and reference domains.
  let E := matrixSequenceExtension ((k+1)-1) Θ.1
  let A := canonicalFCPath base E
  let B := fun t : ℝ => scenarioCorrection base (t • Θ)
  have hA (j : ℕ) : ContDiffAt ℝ 2 (fun t => A t j) 0 := (canonicalFCPath_calculus base E j).1.contDiffAt
  have hB (j : ℕ) : ContDiffAt ℝ 2 (fun t => B t j) 0 := (scenarioCorrection_path_analytic base Θ j).contDiffAt
  have hA0 : A 0=fun _ => cgOperator base := canonicalFCPath_zero base E
  have hB0 : B 0=fun _ => cgOperator base := by
    dsimp only [B]
    rw [zero_smul,scenarioCorrection_zero]
  -- The actual residual/common-tilt splitting uses the same real source-axis derivative as the invisible-fibre theorem.
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
  have hn := correctionFree_invisible_scenario_variation M hfree base hb g k hk hcount Θ hE hInv
  change (exploredFlag base g (k+1)).starProjection
    (cgOperator (metricRoot base)⁻¹ (deriv (fun t : ℝ => probedGradient M.policy (A t) (B t) g (k+1)) 0))=
      residualVariation base g M.policy A B (k+1)-commonTilt base g A (k+1) at ht
  rw [hv,ht] at hn
  exact sub_left_inj.mp hn
end
end krylov.Envelope
