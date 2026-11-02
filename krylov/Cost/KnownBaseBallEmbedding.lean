import krylov.Cost.KnownBaseBallFixed
import krylov.OneGradient.KnownBaseSourceEmbedding

/-!
Article: `main_krylov`, `thm:hier`, complete original source coverage.
Every actual symmetric physical source is reconstructed exactly in the
independent prior/drift coordinates. Their two norms are controlled by
the two separate physical budgets, so the mixed estimate applies to the
whole known base ball and every independently small drift budget.
-/

namespace krylov.Cost
noncomputable section
open Matrix Filter Topology Asymptotics Finset krylov.Reference krylov.Methods
  krylov.OneGradient krylov.Information krylov.Correction krylov.Envelope krylov.Stability krylov.Secant
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Actual prior coordinate of the original physical source. -/
def ballPrior (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (S : Scenario (n+1)) (hbase : S.base.IsSymm) : KnownBasePrior (n+1) :=
  ⟨relativeOperator base (S.base-base), Matrix.isHermitian_iff_isSymm.mpr
    (relativeOperator_isSymm base _ (hbase.sub hb.1.isSymm))⟩

/-- The exact same original physical drift with the prior reset to the
known centre, solely to obtain its independent finite drift coordinates. -/
def ballDriftSource (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (S : Scenario (n+1)) : Scenario (n+1) where
  base := base
  increment := S.increment
  terminal := S.terminal
  correction := S.correction

/-- Actual independent finite drift coordinate of an original source. -/
def ballDrift (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (S : Scenario (n+1)) (hinc : ∀ l<n,(S.increment l).IsSymm) (hterm : S.terminal.IsSymm) :
    symmetricScenarios (n+1) (n+1) :=
  knownBaseSourceParameters base hb (ballDriftSource base S) hb.1.isSymm hinc hterm

/-- The prior coordinate norm is exactly the genuine physical prior budget. -/
theorem ballPrior_norm (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (S : Scenario (n+1)) (hbase : S.base.IsSymm) :
    ‖ballPrior base hb S hbase‖=relativeBudget base (S.base-base) := rfl

/-- Independent actual drift budgets control the drift coordinate without
adding the prior radius, including the exact zero-drift case. -/
theorem ballDrift_norm_le (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (S : Scenario (n+1)) (hinc : ∀ l<n,(S.increment l).IsSymm) (hterm : S.terminal.IsSymm)
    (w : ℝ) (hw : 0≤w) (hquery : ∀ l<n,relativeBudget base (S.increment l)≤w)
    (houtput : relativeBudget base S.terminal≤w) : ‖ballDrift base hb S hinc hterm‖≤w := by
  apply knownBaseSourceParameters_norm_le base hb (ballDriftSource base S) hb.1.isSymm hinc hterm w hw
  · simpa only [ballDriftSource, sub_self, relativeBudget, relativeOperator, Matrix.mul_zero,
      Matrix.zero_mul, chebyshev1.opNorm, norm_zero] using hw
  · exact hquery
  · exact houtput

/-- The independent physical prior/drift chart reconstructs precisely the
original base, each true query increment, and independent output form. -/
theorem ballCoordinates_reconstruct
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef) (hn : 0<n)
    (S : Scenario (n+1)) (hbase : S.base.IsSymm)
    (hinc : ∀ l<n,(S.increment l).IsSymm) (hterm : S.terminal.IsSymm) :
    let T := knownBaseBallSource base (ballPrior base hb S hbase,ballDrift base hb S hinc hterm)
    T.base=S.base ∧ (∀ l<n,T.increment l=S.increment l) ∧ T.terminal=S.terminal := by
  dsimp only
  have hrec := knownBaseSourceParameters_reconstruct base hb hn (ballDriftSource base S)
    hb.1.isSymm hinc hterm
  refine ⟨referenceBaseChart_reconstruct base S.base hb hbase,?_,?_⟩
  · exact hrec.2.1
  · exact hrec.2.2

/-- The literal actual fixed-trial physical output is preserved under the
exact source embedding, including its true history and unqueried output. -/
theorem fixedBallOutput_reconstruct (directions : Bool)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef) (hn : 0<n)
    (g : EuclideanSpace ℝ (Fin (n+1)))
    (S : Scenario (n+1)) (hbase : S.base.IsSymm)
    (hinc : ∀ l<n,(S.increment l).IsSymm) (hterm : S.terminal.IsSymm) :
    fixedBallOutput directions base g (ballPrior base hb S hbase,ballDrift base hb S hinc hterm)=
      fixedScenarioOutput directions base g S := by
  let T := knownBaseBallSource base (ballPrior base hb S hbase,ballDrift base hb S hinc hterm)
  let m := xrfcBasisMethod directions (fixedCGTrial base g)
  have hrec := ballCoordinates_reconstruct base hb hn S hbase hinc hterm
  have hterminal : T.terminal=S.terminal := hrec.2.2
  have hp (k : ℕ) (hk : k≤n) : T.probe k=S.probe k := by
    change T.base+∑ l∈range k,T.increment l=S.base+∑ l∈range k,S.increment l
    rw [hrec.1]
    congr 1
    apply Finset.sum_congr rfl
    intro l hl
    exact hrec.2.1 l ((mem_range.mp hl).trans_le hk)
  have hoperators : oneGradientScenarioMatrices T n=oneGradientScenarioMatrices S n := by
    funext j
    by_cases hj : j≤n
    · rw [oneGradientScenarioMatrices_probe T n j hj, oneGradientScenarioMatrices_probe S n j hj,hp j hj]
    · simp only [oneGradientScenarioMatrices, ite_eq_right hj,Scenario.lastOperator,hp n le_rfl]
      rw [hterminal]
  have hhist : oneGradientRun m T.probeOracle g (n+1)=oneGradientRun m S.probeOracle g (n+1) := by
    rw [← oneGradientScenarioMatrices_histories T n m g (n+1) le_rfl,hoperators,
      oneGradientScenarioMatrices_histories S n m g (n+1) le_rfl]
  have hlast : T.lastOperator n=S.lastOperator n := by
    simp only [Scenario.lastOperator,hp n le_rfl]
    rw [hterminal]
  change m.outputGradient (cgOperator (T.lastOperator n)) (oneGradientRun m T.probeOracle g (n+1))=_
  rw [hlast,hhist]
  rfl

/-- All actual symmetric sources satisfy the fixed known-CG mixed bound
with their independent known-metric prior and drift budgets. -/
theorem fixedCG_known_metric_ball_bound (directions : Bool)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef) (hn : 0<n)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1) :
    ∃ δ C : ℝ,0<δ ∧ 0<C ∧ ∀ r w : ℝ,0≤r → 0≤w → r<δ → w<δ →
      ∀ (S : Scenario (n+1)) (_hbase : S.base.IsSymm)
        (_hinc : ∀ l<n,(S.increment l).IsSymm) (_hterm : S.terminal.IsSymm),
      relativeBudget base (S.base-base)≤r →
      (∀ l<n,relativeBudget base (S.increment l)≤w) → relativeBudget base S.terminal≤w →
      ‖fixedScenarioOutput directions base g S‖≤C*r*w+C*w^2 := by
  obtain ⟨δ,C,hδ,hC,hbound⟩ := fixedBallOutput_mixed_bound directions base hb g hc
  refine ⟨δ,C,hδ,hC,?_⟩
  intro r w hr hw hrδ hwδ S hbase hinc hterm hprior hquery houtput
  let Z := ballPrior base hb S hbase
  let E := ballDrift base hb S hinc hterm
  have hZ : ‖Z‖≤r := by rw [ballPrior_norm]; exact hprior
  have hE : ‖E‖≤w := ballDrift_norm_le base hb S hinc hterm w hw hquery houtput
  have h := hbound Z E (hZ.trans_lt hrδ) (hE.trans_lt hwδ)
  rw [fixedBallOutput_reconstruct directions base hb hn g S hbase hinc hterm] at h
  apply h.trans
  gcongr

end
end krylov.Cost
