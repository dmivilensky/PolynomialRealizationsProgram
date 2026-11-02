import krylov.Cost.KnownBaseBallSource
import krylov.Stability.MixedQuadratic

/-!
Article: `main_krylov`, `thm:hier`.
Derive actual zero output on the whole nearby no-drift axis from full
quadratic termination. Combined with genuine C² regularity and its zero
first jet, this gives the independent C*r*ω+C*ω² source estimate.
-/

namespace krylov.Cost
noncomputable section
open Matrix Filter Topology Asymptotics Finset krylov.Reference krylov.Methods
  krylov.OneGradient krylov.Information krylov.Correction krylov.Envelope krylov.Stability
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- On every nearby genuine full-active positive constant base, the
implemented informed S output vanishes exactly after its complete cycle. -/
theorem knownBaseBallOutput_zero_axis
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1) :
    ∀ᶠ Z : KnownBasePrior (n+1) in 𝓝 0,knownBaseBallOutput false base g (Z,0)=0 := by
  obtain ⟨r,hr,_,hfull⟩ := referenceBaseChart_full_ball base hb g hc
  have hnear : ∀ᶠ Z : KnownBasePrior (n+1) in 𝓝 0,‖Z‖<r := by
    exact (continuous_norm.tendsto 0).eventually (gt_mem_nhds (by simpa using hr))
  filter_upwards [hnear] with Z hZ
  obtain ⟨hB,hcount⟩ := hfull Z hZ.le
  let B := referenceBaseChart base Z
  let S := knownBaseBallSource base (Z,0)
  let trial := informedTrial (cgOperator base)
  let m := xrfcMethod fullMemory trial
  have hinc : ∀ l<n,S.increment l=0 := by
    intro l _
    simp [S, knownBaseBallSource, knownBaseSourceCube, matrixSequenceExtension]
  have hterm : S.terminal=0 := by
    simp [S, knownBaseBallSource, knownBaseSourceCube, matrixSequenceExtension]
  have hop : oneGradientScenarioMatrices S n=fun _ ↦ B :=
    funext (fun j ↦ scenario_operators_zero S hinc hterm j)
  have hhist := oneGradientScenarioMatrices_histories S n m g (n+1) le_rfl
  rw [hop] at hhist
  have hout : S.lastOperator n=B := by
    have h := congrFun hop (n+1)
    rwa [oneGradientScenarioMatrices_output] at h
  change m.outputGradient (cgOperator (S.lastOperator n)) (oneGradientRun m S.probeOracle g (n+1))=0
  rw [hout,← hhist]
  have h := (xrfc_full_terminates B hB g trial
    (fun _ _ ↦ (informed_trial_positive (cgOperator base) _).ne')).2.1
  rwa [hcount] at h

/-- Genuine actual S output bound with independent prior and drift radii;
there is no spurious term depending on the prior alone. -/
theorem knownBaseBallOutput_mixed_bound
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1) :
    ∃ δ C : ℝ,0<δ ∧ 0<C ∧ ∀ Z : KnownBasePrior (n+1),
      ∀ E : symmetricScenarios (n+1) (n+1),‖Z‖<δ → ‖E‖<δ →
        ‖knownBaseBallOutput false base g (Z,E)‖≤C*‖Z‖*‖E‖+C*‖E‖^2 :=
  mixed_quadratic_of_zero_axis (knownBaseBallOutput false base g)
    (knownBaseBallOutput_contDiffAt false base hb g hc)
    (knownBaseBallOutput_hasFDerivAt_zero false base hb g hc)
    (knownBaseBallOutput_zero_axis base hb g hc)

end
end krylov.Cost
