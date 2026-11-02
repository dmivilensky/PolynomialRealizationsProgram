import krylov.OneGradient.KnownBaseCubeExpansion
import krylov.OneGradient.KnownBaseSourceEmbedding
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(b), full original source informed upper tube.
Use: transfer the genuine joint native output bound to every original
physical source, before any source or individual profile is chosen.
Source: exact full-source cube reconstruction and the genuine actual
source oracle/history/output dictionaries, with a common cubic remainder.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Finset krylov.Reference krylov.Methods krylov.Secant krylov.Information
  krylov.Correction krylov.Envelope
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The full original physical source class has one common actual
informed S output upper tube with the sharp correlated K_X coefficient
in true known-reference budgets. Source matrices and every individual
profile are quantified after the same genuine radius and cubic constant.
Use: no smooth source path or supplied output expansion is needed for the
original source-wide asymptotic upper bound.
Article: main_krylov, thm:local(b), original full-source informed upper tube.
Proof: embed every original symmetric physical source exactly in the
existing finite source cube. Its real extended operators and complete
native source history coincide. The common actual cube upper theorem
therefore gives precisely the true original source output estimate. -/
theorem knownBase_full_source_upper_tube_basis (directions : Bool)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef) (hn : 0<n)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1) :
    ∃ delta C : ℝ,0<delta ∧ 0<C ∧ ∀ (S : Scenario (n+1)) (hbase : S.base.IsSymm)
      (hinc : ∀ l<n,(S.increment l).IsSymm) (hterm : S.terminal.IsSymm),
      ‖knownBaseSourceParameters base hb S hbase hinc hterm‖<delta →
      ∀ (omega : ℕ → ℝ) (w c : ℝ),
      (∀ l<n,relativeBudget base (S.increment l)≤omega l) →
      relativeBudget base S.terminal≤w → relativeBudget base (S.base-base)≤c →
      ‖cgOperator (metricRoot base)⁻¹ (informedScenarioOutput directions base g S)‖≤
        ‖cgCanonicalError base g n‖*informedConstant (∑ l∈range n,omega l) w c+
          C*‖knownBaseSourceParameters base hb S hbase hinc hterm‖^3 := by
  obtain ⟨delta,C,hd,hC,hcube⟩ := knownBaseSourceCube_basis_uniform_upper directions base hb g hc
  refine ⟨delta,C,hd,hC,?_⟩
  intro S hbase hinc hterm hsmall omega w c hquery houtput hprior
  let Theta := knownBaseSourceParameters base hb S hbase hinc hterm
  let T := knownBaseSourceCube base Theta
  let m := xrfcBasisMethod directions (informedTrial (cgOperator base))
  have hrec := knownBaseSourceParameters_reconstruct base hb hn S hbase hinc hterm
  have hoperators : oneGradientScenarioMatrices T n=oneGradientScenarioMatrices S n :=
    knownBaseSourceParameters_operators base hb hn S hbase hinc hterm
  have hhistory : oneGradientRun m T.probeOracle g (n+1)=oneGradientRun m S.probeOracle g (n+1) := by
    rw [← oneGradientScenarioMatrices_histories T n m g (n+1) le_rfl,hoperators,
      oneGradientScenarioMatrices_histories S n m g (n+1) le_rfl]
  have hlast : T.lastOperator n=S.lastOperator n := by
    simpa only [oneGradientScenarioMatrices_output] using congrFun hoperators (n+1)
  have h := hcube Theta hsmall omega w c
    (fun l hl => by rw [hrec.2.1 l hl];exact ⟨hinc l hl,hquery l hl⟩)
    (by rw [hrec.2.2];exact houtput) (by rw [hrec.1];exact hprior)
  change ‖cgOperator (metricRoot base)⁻¹
    (m.outputGradient (cgOperator (T.lastOperator n)) (oneGradientRun m T.probeOracle g (n+1)))‖≤_ at h
  rw [hlast,hhistory] at h
  exact h

/-- The original S specialization of the common native-basis theorem.
Use: preserve the established step-policy physical source interface.
Article: main_krylov, thm:local(b).
Proof: specialize the shared genuine physical theorem to the S basis. -/
theorem knownBase_full_source_upper_tube
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef) (hn : 0<n)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1) :
    ∃ delta C : ℝ,0<delta ∧ 0<C ∧ ∀ (S : Scenario (n+1)) (hbase : S.base.IsSymm)
      (hinc : ∀ l<n,(S.increment l).IsSymm) (hterm : S.terminal.IsSymm),
      ‖knownBaseSourceParameters base hb S hbase hinc hterm‖<delta →
      ∀ (omega : ℕ → ℝ) (w c : ℝ),
      (∀ l<n,relativeBudget base (S.increment l)≤omega l) →
      relativeBudget base S.terminal≤w → relativeBudget base (S.base-base)≤c →
      ‖cgOperator (metricRoot base)⁻¹ (informedScenarioOutput false base g S)‖≤
        ‖cgCanonicalError base g n‖*informedConstant (∑ l∈range n,omega l) w c+
          C*‖knownBaseSourceParameters base hb S hbase hinc hterm‖^3  := by
  exact knownBase_full_source_upper_tube_basis false base hb hn g hc

end
end krylov.OneGradient
