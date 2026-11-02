import krylov.Information.FullModelQuery
import krylov.Information.PreQuadraticCentreBounds

/-!
Article: main_krylov, s4:cor-Q, actual centred physical RFC solve.
Use: prove the true final gate, correction query, returned gradient and
common-twin information radius for the original pre-quadratic source.
Source: genuine CG prefix shadow, exact square physical model solve and
the proved actual common-centre reflection and robust two-scenario radius.
-/

namespace krylov.Information
noncomputable section
open Matrix Finset krylov.Reference krylov.Methods krylov.Secant krylov.Correction krylov.Stability krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n N : ℕ}

/-- The actual final RFC phase makes precisely the centred physical query and records its true returned gradient and complete one-query trace.
Use: Establish the genuine centred solve for the actual policy, including its observed-data gate.
Article: main_krylov, s4:cor-Q, genuine centred RFC execution.
Proof: The old actually measured pairs are true quadratic CG pairs, so their actual normalized defect is zero and the nonempty gate passes. Genuine full CG rank proves the real basis inverse domain; the actual native model is the proved common centre. Execute that true one-query correction tree. -/
theorem Scenario.PreQuadratic.rfc_phase_centre {S : Scenario (N+1)}
    {Q : Matrix (Fin (N+1)) (Fin (N+1)) ℝ} (hQ : Q.PosDef)
    {g : EuclideanSpace ℝ (Fin (N+1))} (hcount : referenceAtomCount Q hQ g=N+1)
    (h : S.PreQuadratic (cgOperator Q) g N) (hN : 0<N) :
    let m := rfcMethod fullMemory 1
    let gp := S.preQuadraticIncoming Q g
    let u := -(cgOperator (S.preQuadraticCentre Q g)⁻¹ gp)
    probedPhase m S.probeOracle (S.correctionOracle N) g N=
      ⟨u,gp+cgOperator (S.lastOperator N) u,[(u,gp+cgOperator (S.lastOperator N) u)]⟩ := by
  -- First derive the true old-data gate and full physical basis inverse domain.
  dsimp only
  let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin (N+1)))
  have hm := rfcMethod_consistent fullMemory (fun _ ha => ha) 1 (E := EuclideanSpace ℝ (Fin (N+1)))
  have hp := cgOperator_positive Q hQ
  let U := probedStepBasis m S.probeOracle (S.correctionOracle N) g N
  let Y := probedImageBasis m S.probeOracle (S.correctionOracle N) g N
  have hy (i : Fin N) : probedSecant m S.probeOracle (S.correctionOracle N) g (N-1-i.val)=
      cgOperator Q (probedStep m S.probeOracle (S.correctionOracle N) g (N-1-i.val)) := by
    have hi : N-1-i.val<N := by have := i.isLt; omega
    rw [h.secant hp.1 hp.2 m hm hi,h.step hp.1 hp.2 m hm hi]
  have hd := pairDefect_quadratic
    (fun i : Fin N => probedStep m S.probeOracle (S.correctionOracle N) g (N-1-i.val)) (cgOperator Q) hp.1
  have hz : pairDefect
      (fun i : Fin N => probedStep m S.probeOracle (S.correctionOracle N) g (N-1-i.val))
      (fun i : Fin N => probedSecant m S.probeOracle (S.correctionOracle N) g (N-1-i.val))=0 := by
    rw [funext hy]
    exact hd
  have hi := h.incoming hQ m hm
  have hU : IsUnit (fullBasisMatrix U).det := by
    dsimp only [U]
    rw [h.rfc_stepBasis hQ]
    exact fullBasisMatrix_unit _ (probedStepBasis_independent _ hm _ hp.1 hp.2 g N
      (fun i hi => cg_nonstagnation Q hQ g i (by omega)))
  have hq := full_model_query U (pairModel U Y) hU (S.preQuadraticIncoming Q g)
  rw [h.rfc_model_centre hQ hcount] at hq
  have he := probedRFC_phase_array fullMemory 1 S.probeOracle (S.correctionOracle N) g N
  rw [show min (fullMemory N) N=N from min_self N] at he
  have hgate : 0<N ∧ ‖pairDefect
      (fun i : Fin N => probedStep m S.probeOracle (S.correctionOracle N) g (N-1-i.val))
      (fun i : Fin N => probedSecant m S.probeOracle (S.correctionOracle N) g (N-1-i.val))‖<1 := by
    rw [hz]
    exact ⟨hN,by simp⟩
  rw [he,rfcArrayPhase,ite_eq_left hgate]
  change runCorrections (repeatedModelTree U (pairModel U Y) 1 _) _ _=_
  rw [hi]
  simp only [repeatedModelTree,runCorrections,hq,add_zero]
  simp only [Scenario.correctionOracle,ite_eq_right (show ¬ N<N from by omega)]


/-- The real final RFC output is its common incoming gradient plus the actual terminal operator on the genuine centred query.
Use: Use the actual executed returned gradient in the source information comparison.
Article: main_krylov, s4:cor-Q, genuine centred RFC execution.
Proof: Read the returned-gradient field from the independently proved complete real final phase. -/
theorem Scenario.PreQuadratic.rfc_gradient_centre {S : Scenario (N+1)}
    {Q : Matrix (Fin (N+1)) (Fin (N+1)) ℝ} (hQ : Q.PosDef)
    {g : EuclideanSpace ℝ (Fin (N+1))} (hcount : referenceAtomCount Q hQ g=N+1)
    (h : S.PreQuadratic (cgOperator Q) g N) (hN : 0<N) :
    probedGradient (rfcMethod fullMemory 1) S.probeOracle (S.correctionOracle N) g (N+1)=
      S.preQuadraticIncoming Q g+cgOperator (S.lastOperator N)
        (-(cgOperator (S.preQuadraticCentre Q g)⁻¹ (S.preQuadraticIncoming Q g))) := by
  exact congrArg CorrectionResult.gradient (h.rfc_phase_centre hQ hcount hN)

/-- The real final RFC output equals the true hidden terminal error applied to its actual centred correction.
Use: Identify the actual RFC residual with the source hidden-curvature radius.
Article: main_krylov, s4:cor-Q, genuine centred RFC execution.
Proof: The genuine centre inverse solves Ju=−g′. Subtract that exact physical equation from the actual terminal gradient update. -/
theorem Scenario.PreQuadratic.rfc_gradient_hidden {S : Scenario (N+1)}
    {Q : Matrix (Fin (N+1)) (Fin (N+1)) ℝ} (hQ : Q.PosDef)
    {g : EuclideanSpace ℝ (Fin (N+1))} (hcount : referenceAtomCount Q hQ g=N+1)
    (h : S.PreQuadratic (cgOperator Q) g N) (hN : 0<N)
    (hJ : IsUnit (S.preQuadraticCentre Q g).det) :
    probedGradient (rfcMethod fullMemory 1) S.probeOracle (S.correctionOracle N) g (N+1)=
      cgOperator (S.lastOperator N-S.preQuadraticCentre Q g)
        (-(cgOperator (S.preQuadraticCentre Q g)⁻¹ (S.preQuadraticIncoming Q g))) := by
  -- The genuine centre equation cancels the original incoming physical gradient.
  let J := S.preQuadraticCentre Q g
  let gp := S.preQuadraticIncoming Q g
  have hjunit : IsUnit J.det := hJ
  have hj : cgOperator J (-(cgOperator J⁻¹ gp))=-gp := by
    simp only [map_neg,cgOperator,← mul_apply_eq_comp,← map_mul,mul_nonsing_inv J hjunit,map_one,one_apply_eq_self]
  rw [h.rfc_gradient_centre hQ hcount hN]
  change gp+cgOperator (S.lastOperator N) (-(cgOperator J⁻¹ gp))=cgOperator (S.lastOperator N-J) (-(cgOperator J⁻¹ gp))
  simp only [cgOperator] at hj
  simp only [cgOperator,map_sub,_root_.sub_apply,hj,sub_neg_eq_add,add_comm]

/-- The genuine common-twin output radius for every original one-correction CG-consistent method is the actual RFC output norm divided by the robust inverse-model factor.
Use: Replace the abstract centre numerator by the actual RFC returned residual in the original physical base metric.
Article: main_krylov, s4:cor-Q, genuine centred RFC execution.
Proof: The actual centred RFC execution leaves precisely the hidden-curvature action. Exact root transport identifies its true normalized norm with the existing common-terminal information-radius numerator. -/
theorem Scenario.PreQuadratic.common_radius_rfc {S : Scenario (N+1)}
    {Q : Matrix (Fin (N+1)) (Fin (N+1)) ℝ} (hQ : Q.PosDef)
    {g : EuclideanSpace ℝ (Fin (N+1))} (hcount : referenceAtomCount Q hQ g=N+1)
    (h : S.PreQuadratic (cgOperator Q) g N) (hN : 0<N) (hbase : S.base.PosDef)
    (hE : ∀ i<N, (S.increment i).IsSymm) (hJ : IsUnit (S.preQuadraticCentre Q g).det)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1)))) (hm : CGConsistent m) (h1 : OneCorrectionMethod m) :
    let J := S.preQuadraticCentre Q g
    let Δ := S.lastOperator N-J
    let K := cgOperator (relativeOperator S.base Δ*(relativeOperator S.base J)⁻¹)
    ‖cgOperator (metricRoot S.base)⁻¹
      (probedGradient (rfcMethod fullMemory 1) S.probeOracle (S.correctionOracle N) g (N+1))‖/Real.sqrt (1+‖K‖^2)≤
      max ‖cgOperator (metricRoot S.base)⁻¹ (probedGradient m S.probeOracle (S.correctionOracle N) g (N+1))‖
        ‖cgOperator (metricRoot S.base)⁻¹ (probedGradient m (S.preQuadraticTwin Q g).probeOracle
          ((S.preQuadraticTwin Q g).correctionOracle N) g (N+1))‖ := by
  -- The real centred execution supplies the exact normalized robust-radius numerator.
  let J := S.preQuadraticCentre Q g
  let Δ := S.lastOperator N-J
  let gp := S.preQuadraticIncoming Q g
  have hr := h.common_terminal_radius hQ hcount hbase hE hJ m hm h1
  have hn := normalized_centre_numerator S.base J Δ hbase gp
  have ha := canonical_form_action S.base Δ hbase (-(cgOperator J⁻¹ gp))
  change cgOperator (relativeOperator S.base Δ) (cgOperator (metricRoot S.base) (-(cgOperator J⁻¹ gp)))=
    cgOperator (metricRoot S.base)⁻¹ (cgOperator Δ (-(cgOperator J⁻¹ gp))) at ha
  rw [ha,← h.rfc_gradient_hidden hQ hcount hN hJ] at hn
  dsimp only at hr ⊢
  rwa [hn] at hr

end
end krylov.Information
