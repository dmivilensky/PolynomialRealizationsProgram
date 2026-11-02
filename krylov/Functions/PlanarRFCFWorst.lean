import krylov.Functions.PlanarRFCFResponse
import krylov.Functions.PlanarAttainedChord

/-!
Article: main_krylov, thm:Fplanar, the genuine RFC-F supremum coefficient.
Use: take the worst actual output gradient over the full scalar cubic family
and retain the original C_Y, with a proved uniform fourth-order remainder.
Source: compactness of the real diagonal tensor ball, actual observed model
execution, true gradient expansion and the proved binary cubic norm bounds.
-/
namespace krylov.Functions
noncomputable section
open Set Metric Matrix krylov.Tensor.BinaryCubic
open scoped InnerProductSpace Matrix.Norms.L2Operator

/-- The original binary tensor ball is compact in its four actual coefficients.
Article: main_krylov, thm:Fplanar. -/
theorem binaryFromVector_inBall_isCompact :
    IsCompact {q : Fin 4 → ℝ | (binaryFromVector q).InBall} := by
  apply (isCompact_closedBall (0 : Fin 4 → ℝ) 1).of_isClosed_subset binaryFromVector_inBall_isClosed
  intro q hq
  have hh := binaryCoefficientVector_bound hq
  rw [binaryCoefficientVector_fromVector] at hh
  simpa only [mem_closedBall,dist_zero_right] using hh

/-- An actual admissible tensor attains the complete RFC-F objective supremum.
Article: main_krylov, thm:Fplanar, C_Y is a genuine attained worst case. -/
theorem exists_tensor_attaining_rfcWorst (r : ℝ) :
    ∃ t : krylov.Tensor.BinaryCubic, t.InBall ∧ rfcObjective r t=rfcWorst r := by
  let S := {q : Fin 4 → ℝ | (binaryFromVector q).InBall}
  let F := fun q : Fin 4 → ℝ=>rfcObjective r (binaryFromVector q)
  have hne : S.Nonempty := ⟨binaryCoefficientVector harmonicSine,by
    change (binaryFromVector (binaryCoefficientVector harmonicSine)).InBall
    rw [binaryFromVector_coefficientVector]
    exact harmonicSine_inBall⟩
  have hc : Continuous F := by unfold F rfcObjective binaryFromVector; fun_prop
  obtain ⟨q,hq,hmax⟩ := binaryFromVector_inBall_isCompact.exists_isMaxOn hne hc.continuousOn
  refine ⟨binaryFromVector q,hq,le_antisymm ?_ ?_⟩
  · exact le_csSup (rfcValues_bddAbove r) ⟨_,hq,rfl⟩
  · apply csSup_le ⟨2,two_mem_rfcValues r⟩
    rintro v ⟨t,ht,rfl⟩
    have hm : binaryCoefficientVector t∈S := by
      change (binaryFromVector (binaryCoefficientVector t)).InBall
      rw [binaryFromVector_coefficientVector]
      exact ht
    have hb : F (binaryCoefficientVector t)≤F q := hmax hm
    simpa only [F,binaryFromVector_coefficientVector] using hb

/-- The real worst output-gradient norm of the actual observed RFC-F solve.
Article: main_krylov, thm:Fplanar. -/
def planeRFCFActualWorst (p r : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ t : krylov.Tensor.BinaryCubic, t.InBall ∧
    v=‖gradient (planeCubicObjective p r t) (planeRFCFOutput p r t)‖}

set_option maxHeartbeats 800000 in
/-- The actual scalar-source RFC-F worst case has exactly C_Y as its leading
coefficient: its absolute error is uniformly fourth order. The first/last
reference product is r*p³/4, hence this is precisely the printed model-metric
coefficient C_Y(r), whose two-sided bounds were proved on the true tensor ball.
Article: main_krylov, thm:Fplanar. -/
theorem planeRFCFActualWorst_remainder (r : ℝ) (hr : 0<r) :
    ∃ ε₀ C : ℝ, 0<ε₀ ∧ 0<C ∧ ∀ p : ℝ, 0<p → p<ε₀ →
      |planeRFCFActualWorst p r-(r/4*modelMetricCoefficient r)*p^3|≤C*p^4 := by
  obtain ⟨ep,C,hep,hC,hrem⟩ := planeRFCFOutput_gradient_remainder r hr.ne'
  obtain ⟨tstar,htstar,hstar⟩ := exists_tensor_attaining_rfcWorst r
  refine ⟨ep,C,hep,hC,?_⟩
  intro p hp he
  let K := (r/4*modelMetricCoefficient r)*p^3
  have hcoeff : r^2/4*rfcWorst r*p^3=K := by dsimp only [K,modelMetricCoefficient]; ring
  have hnorm (t : krylov.Tensor.BinaryCubic) (ht : t.InBall) :
      |‖gradient (planeCubicObjective p r t) (planeRFCFOutput p r t)‖-
        r^2/4*rfcObjective r t*p^3|≤C*p^4 := by
    have hh := abs_norm_sub_norm_le (gradient (planeCubicObjective p r t) (planeRFCFOutput p r t))
      (-p^3 • ((planeTerminalOperator r t-planeRFCFModelOperator r t) (planeTerminalRho r t)))
    rw [neg_smul,sub_neg_eq_add] at hh
    rw [norm_neg,norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hp.le 3),planeRFCF_leading_norm] at hh
    rw [show p^3*(r^2/4*rfcObjective r t)=r^2/4*rfcObjective r t*p^3 by ring] at hh
    exact hh.trans (hrem p hp he t ht)
  let V := {v : ℝ | ∃ t : krylov.Tensor.BinaryCubic, t.InBall ∧
    v=‖gradient (planeCubicObjective p r t) (planeRFCFOutput p r t)‖}
  have hne : V.Nonempty := ⟨_,tstar,htstar,rfl⟩
  have hupper v (hv : v∈V) : v≤K+C*p^4 := by
    obtain ⟨t,ht,rfl⟩ := hv
    have hh := (abs_le.mp (hnorm t ht)).2
    have hb := le_csSup (rfcValues_bddAbove r) (show rfcObjective r t∈rfcValues r from ⟨t,ht,rfl⟩)
    have hc := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by positivity : 0≤r^2/4)) (pow_nonneg hp.le 3)
    change r^2/4*rfcObjective r t*p^3≤r^2/4*rfcWorst r*p^3 at hc
    rw [hcoeff] at hc
    linarith only [hh,hc]
  have hbounded : BddAbove V := ⟨K+C*p^4,hupper⟩
  have hWupper : planeRFCFActualWorst p r≤K+C*p^4 := csSup_le hne hupper
  have hWlower : K-C*p^4≤planeRFCFActualWorst p r := by
    have hh := (abs_le.mp (hnorm tstar htstar)).1
    rw [hstar,hcoeff] at hh
    have hm : ‖gradient (planeCubicObjective p r tstar) (planeRFCFOutput p r tstar)‖≤
        planeRFCFActualWorst p r := le_csSup hbounded ⟨tstar,htstar,rfl⟩
    linarith only [hh,hm]
  change |planeRFCFActualWorst p r-K|≤C*p^4
  exact abs_le.mpr ⟨by linarith only [hWlower],by linarith only [hWupper]⟩

end
end krylov.Functions
