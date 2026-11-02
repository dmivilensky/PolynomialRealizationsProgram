import krylov.Information.CommonTwinCentre
import krylov.Information.PlanarTerminalExecution
import krylov.Information.PhysicalRadius

/-!
Article: main_krylov, s4:cor-Q, genuine common terminal information geometry.
Use: the actual common physical pre-quadratic twin has opposite terminal
operators about its true observed centre; every original one-correction
method sees the same actual incoming gradient and one common correction.
Source: real common-prefix/probe preservation, finite-horizon physical
reflection and the existing exact actual one-query robust radius theorem.
-/

namespace krylov.Information
noncomputable section
open Matrix Finset krylov.Reference krylov.Methods krylov.Secant krylov.Correction krylov.Stability krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {N : ℕ}

/-- The actual common terminal post-search gradient determined by the genuine pre-quadratic reference prefix and original last physical probe.
Use: all competing methods have this same true incoming physical gradient, independently of their allowed positive direction scale.
Article: main_krylov, s4:cor-Q, genuine common terminal incoming gradient. -/
def Scenario.preQuadraticIncoming (S : Scenario (N+1)) (Q : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (N+1))) : EuclideanSpace ℝ (Fin (N+1)) :=
  searchedGradient (CG.gradient (cgOperator Q) g N) (CG.direction (cgOperator Q) g N)
    (S.probeOracle N (CG.direction (cgOperator Q) g N))

/-- Every genuinely CG-consistent method has exactly the same actual terminal post-search gradient on the original pre-quadratic source.
Use: the common terminal information obstruction uses a real method-independent incoming state.
Article: main_krylov, s4:cor-Q, actual common terminal information radius.
Proof: the actual observed prefix gradient is the true reference one, and the actual final direction and probe share its positive CG scale. The proved exact-search scaling identity cancels that original scalar. -/
theorem Scenario.PreQuadratic.incoming {S : Scenario (N+1)}
    {Q : Matrix (Fin (N+1)) (Fin (N+1)) ℝ} (hQ : Q.PosDef)
    {g : EuclideanSpace ℝ (Fin (N+1))} (h : S.PreQuadratic (cgOperator Q) g N)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1)))) (hm : CGConsistent m) :
    let H := methodRun m S.probeOracle (S.correctionOracle N) g N
    let d := m.direction H
    searchedGradient H.gradient d (S.probeOracle N d)=S.preQuadraticIncoming Q g := by
  have hp := cgOperator_positive Q hQ
  obtain ⟨c,hc,hd⟩ := h.direction hp.1 hp.2 m hm le_rfl
  change searchedGradient (probedGradient m S.probeOracle (S.correctionOracle N) g N)
    (probedDirection m S.probeOracle (S.correctionOracle N) g N)
    (S.probeOracle N (probedDirection m S.probeOracle (S.correctionOracle N) g N))=_
  rw [h.gradient hp.1 hp.2 m hm le_rfl,hd,map_smul,searchedGradient_smul _ _ _ hc.ne']
  rfl


/-- Every genuine one-correction CG-consistent method returns the actual common incoming gradient plus one common physical correction acted on by the two actual common-twin terminal operators.
Use: the information-radius comparison applies to real executed output gradients of the full source method class.
Article: main_krylov, s4:cor-Q, actual common terminal information radius.
Proof: the actual complete histories and final probes agree on the common physical twin. Therefore the true data-only correction decision has the same real first query. The genuine at-most-one-query execution theorem gives the actual returned gradient on each physical source, with the proved common incoming state. -/
theorem Scenario.PreQuadratic.common_terminal_form {S : Scenario (N+1)}
    {Q : Matrix (Fin (N+1)) (Fin (N+1)) ℝ} (hQ : Q.PosDef)
    {g : EuclideanSpace ℝ (Fin (N+1))} (hcount : referenceAtomCount Q hQ g=N+1)
    (h : S.PreQuadratic (cgOperator Q) g N)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1)))) (hm : CGConsistent m) (h1 : OneCorrectionMethod m) :
    ∃ u : EuclideanSpace ℝ (Fin (N+1)),
      probedGradient m S.probeOracle (S.correctionOracle N) g (N+1)=
        S.preQuadraticIncoming Q g+cgOperator (S.lastOperator N) u ∧
      probedGradient m (S.preQuadraticTwin Q g).probeOracle ((S.preQuadraticTwin Q g).correctionOracle N) g (N+1)=
        S.preQuadraticIncoming Q g+cgOperator ((S.preQuadraticTwin Q g).lastOperator N) u := by
  -- The genuine original common history and last probe fix the same actual first correction query.
  let H := methodRun m S.probeOracle (S.correctionOracle N) g N
  let d := m.direction H
  let z := S.probeOracle N d
  let u := firstCorrectionStep (m.correction H z)
  have hh := h.twin_run hQ hcount m hm (le_refl N)
  have hz := h.twin_last_probe hQ hcount m hm
  have hzt : (S.preQuadraticTwin Q g).probeOracle N d=z := by
    unfold probedProbe probedDirection at hz
    rw [← hh] at hz
    exact hz.symm
  have hi := h.incoming hQ m hm
  refine ⟨u,?_,?_⟩
  · change (runCorrections (m.correction H z) (S.correctionOracle N N) (searchedGradient H.gradient d z)).gradient=_
    rw [one_correction_gradient _ (h1 H z),hi]
    simp only [Scenario.correctionOracle,ite_eq_right (show ¬ N<N from by omega)]
    rfl
  · change (runCorrections (m.correction (methodRun m _ _ g N) _)
      ((S.preQuadraticTwin Q g).correctionOracle N N) _).gradient=_
    rw [← hh]
    change (runCorrections (m.correction H ((S.preQuadraticTwin Q g).probeOracle N d)) _
      (searchedGradient H.gradient d ((S.preQuadraticTwin Q g).probeOracle N d))).gradient=_
    rw [hzt,one_correction_gradient _ (h1 H z),hi]
    simp only [Scenario.correctionOracle,ite_eq_right (show ¬ N<N from by omega)]
    rfl


/-- The true terminal outputs of every original one-correction CG-consistent method satisfy the common physical robust lower radius of the actual pre-quadratic twin pair.
Use: the common-centre information obstruction concerns real source executions rather than an assumed correction-output formula.
Article: main_krylov, s4:cor-Q, actual common terminal information radius.
Proof: the genuine one-query terminal executor gives the same actual physical correction for both sources. Their true terminal matrices are opposite about the observed common centre. Apply the already proved physical normalized two-scenario radius on its genuine centre inverse domain and identify both actual returned gradients. -/
theorem Scenario.PreQuadratic.common_terminal_radius {S : Scenario (N+1)}
    {Q : Matrix (Fin (N+1)) (Fin (N+1)) ℝ} (hQ : Q.PosDef)
    {g : EuclideanSpace ℝ (Fin (N+1))} (hcount : referenceAtomCount Q hQ g=N+1)
    (h : S.PreQuadratic (cgOperator Q) g N) (hbase : S.base.PosDef)
    (hE : ∀ i<N, (S.increment i).IsSymm)
    (hJ : IsUnit (S.preQuadraticCentre Q g).det)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1)))) (hm : CGConsistent m) (h1 : OneCorrectionMethod m) :
    let J := S.preQuadraticCentre Q g
    let Δ := S.lastOperator N-J
    let K := cgOperator (relativeOperator S.base Δ*(relativeOperator S.base J)⁻¹)
    ‖K (cgOperator (metricRoot S.base)⁻¹ (S.preQuadraticIncoming Q g))‖/Real.sqrt (1+‖K‖^2)≤
      max ‖cgOperator (metricRoot S.base)⁻¹ (probedGradient m S.probeOracle (S.correctionOracle N) g (N+1))‖
        ‖cgOperator (metricRoot S.base)⁻¹ (probedGradient m (S.preQuadraticTwin Q g).probeOracle
          ((S.preQuadraticTwin Q g).correctionOracle N) g (N+1))‖ := by
  -- Insert the true executed terminal outputs in the existing genuine physical robust radius.
  obtain ⟨u,hs,ht⟩ := h.common_terminal_form hQ hcount m hm h1
  let J := S.preQuadraticCentre Q g
  let Δ := S.lastOperator N-J
  have hp : J+Δ=S.lastOperator N := by dsimp only [Δ]; abel
  have hn : J-Δ=(S.preQuadraticTwin Q g).lastOperator N := by
    rw [S.preQuadraticTwin_terminal Q hQ g hcount hbase.1.isSymm hE]
    dsimp only [J,Δ]
    module
  have hr := normalized_two_scenario_lower S.base J Δ hbase hJ (S.preQuadraticIncoming Q g) u
  dsimp only at hr ⊢
  rw [hp,hn,← hs,← ht] at hr
  exact hr

end
end krylov.Information
