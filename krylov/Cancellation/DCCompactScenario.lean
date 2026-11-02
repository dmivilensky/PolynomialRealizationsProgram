import krylov.Cancellation.DCCompactSymmetricScenario
import krylov.Methods.CorrectionFreeOracles
import krylov.Envelope.ScenarioVariation
set_option autoImplicit false
/-!
Article: main_krylov, apH:dcs2(b), compact-uniform original finite matrix sources.
Use: cover all original symmetric increment matrices simultaneously while
keeping the actual correction-free executor and every original source slot.
Source: the proved true symmetric-scenario compact C-one expansion and exact
native correction-operator independence; replacing unused slots decreases norm.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix Set Filter krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Variation krylov.Correction krylov.Envelope
open scoped Topology Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X] {n : ℕ}

/-- One genuine compact-uniform C-one quadratic output remainder holds for
every original finite symmetric increment scenario of consistent DC-slide.
Use: every original matrix budget and its matrices share the same actual
radius and constant; unread correction slots are not extra assumptions.
Article: main_krylov, apH:dcs2(b), full original finite-source uniformity.
Proof: retain the actual symmetric source increments in the proved true
symmetric scenario space and set only the unused correction slots to zero.
This decreases the true source norm. Exact correction-free native history
independence identifies the original returned gradient, so its genuine
compact quadratic bound applies to the original finite scenario. -/
theorem dc_slide_consistent_compact_scenario_expansion
    (estimate : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (k : ℕ) (hfull : k+1=n) (K : Set X) (hK : IsCompact K)
    (hbsym : ∀ x,(base x).IsSymm)
    (hb : ∀ x∈K,ContDiffAt ℝ 1 base x) (hpos : ∀ x∈K,∀ᶠ p in 𝓝 x,(base p).PosDef)
    (hg : ∀ x∈K,ContDiffAt ℝ 1 g x)
    (hcount : ∀ x (hx : x∈K),referenceAtomCount (base x) (hpos x hx).self_of_nhds (g x)=n)
    (ha : ∀ x∈K,∀ j<n,
      let Q := cgOperator (base x)
      let H := methodRun (dcSlideMethod fullMemory estimate) (fun _ => Q) (fun _ => Q) (g x) j
      ContDiffAt ℝ 1 (historyEstimateChart estimate H.queryShape H.observationList.length)
        (observedArray H.observationList.length H.observationList))
    (ha0 : ∀ x∈K,∀ j<n,0<estimate (methodRun (dcSlideMethod fullMemory estimate)
      (fun _ => cgOperator (base x)) (fun _ => cgOperator (base x)) (g x) j))
    (hcal : ∀ x∈K,∀ j<n,estimate (methodRun (dcSlideMethod fullMemory estimate)
      (fun _ => cgOperator (base x)) (fun _ => cgOperator (base x)) (g x) j)=CG.length (cgOperator (base x)) (g x) j) :
    let m := dcSlideMethod fullMemory estimate
    ∃ delta C : ℝ,0<delta ∧ 0≤C ∧ ∀ x∈K,∀ Theta : CanonicalScenario n (k+1),‖Theta‖≤delta →
      (∀ l,(Theta.1 l).IsSymm) →
      let R := cgOperator (metricRoot (base x))⁻¹
      ‖R (scenarioGradient m (base x) (g x) (k+1) Theta)-
        deferredResponse (base x) (g x) k 0 (matrixSequenceExtension ((k+1)-1) Theta.1)‖≤C*‖Theta‖^2*‖R (g x)‖ := by
  let m := dcSlideMethod fullMemory estimate
  obtain ⟨delta,C,hd,hC,hbound⟩ := dc_slide_consistent_compact_symmetric_scenario estimate base g k hfull K hK
    hbsym hb hpos hg hcount ha ha0 hcal
  refine ⟨delta,C,hd,hC,?_⟩
  intro x hx Theta hnorm hTheta
  let Theta0 : symmetricScenarios n (k+1) := ⟨(Theta.1,0),hTheta,fun _ => Matrix.isSymm_zero⟩
  have hn : ‖Theta0‖≤‖Theta‖ := by
    change max ‖Theta.1‖ ‖(0 : Fin (k+1) → Matrix (Fin n) (Fin n) ℝ)‖≤max ‖Theta.1‖ ‖Theta.2‖
    rw [norm_zero,max_eq_left (norm_nonneg _)]
    exact le_max_left _ _
  have he := hbound x hx Theta0 (hn.trans hnorm)
  have hhistory := correctionFree_run_independent m (dc_slide_correction_free fullMemory estimate)
    (scenarioProbe (base x) Theta) (scenarioCorrection (base x) Theta0.val) (scenarioCorrection (base x) Theta) (g x) n
  have hG : probedGradient m (scenarioProbe (base x) Theta) (scenarioCorrection (base x) Theta0.val) (g x) n=
      probedGradient m (scenarioProbe (base x) Theta) (scenarioCorrection (base x) Theta) (g x) n :=
    congrArg History.gradient hhistory
  have hN : probedGradient m (scenarioProbe (base x) Theta) (scenarioCorrection (base x) Theta) (g x) n=
      probedGradient m (scenarioProbe (base x) Theta) (scenarioCorrection (base x) Theta) (g x) (k+1) :=
    congrArg (fun j : ℕ => probedGradient m (scenarioProbe (base x) Theta)
      (scenarioCorrection (base x) Theta) (g x) j) hfull.symm
  change ‖cgOperator (metricRoot (base x))⁻¹
    (probedGradient m (scenarioProbe (base x) Theta) (scenarioCorrection (base x) Theta0.val) (g x) n)-
      deferredResponse (base x) (g x) k 0 (matrixSequenceExtension ((k+1)-1) Theta.1)‖≤
      C*‖Theta0‖^2*‖cgOperator (metricRoot (base x))⁻¹ (g x)‖ at he
  rw [hG,hN] at he
  exact he.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg Theta0) (norm_nonneg Theta)).mpr hn) hC) (norm_nonneg _))

end
end krylov.Cancellation
