import krylov.Convergence.ObservableSelfConcordant

/-!
Article: main_krylov, apG:Dunif, genuine proper-domain source precision.
Use: the same universal local source on an open convex self-concordant
domain containing the prescribed canonical neighbourhood. No global
self-concordance or behaviour outside that real neighbourhood is used.
Source: Nesterov18 local Hessian comparison, actual derivative uniqueness
and the true positive-root coordinate pullback. Domain inclusion is stated
explicitly; arbitrary truncations of a self-concordant germ do not imply it.
-/
namespace krylov.Convergence
noncomputable section
open Set Metric Matrix krylov.Functions krylov.Nonlinear krylov.Reference
open scoped InnerProductSpace NNReal
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- A genuine self-concordant function on a proper open convex domain
supplies exactly the same universal scalar source once its canonical
1/8-ball lies in that domain. Article: main_krylov, apG:Dunif. -/
theorem observable_selfConcordant_domain_source
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (f : E → ℝ) (U : Set E) (D : StandardSelfConcordantData f U)
    (hgzero : gradient f 0=0) (hH : D.hessian 0=cgOperator base)
    (hdomain : ball (0:E) (1/8)⊆(metricCoordinates base hb).symm ⁻¹' U) :
    ObservableLocalSource (metricCoordinates base hb) f (gradient f) D.hessian (1/64) 4 := by
  let T:=metricCoordinates base hb
  let V:=T.symm ⁻¹' U
  have hT:=metricCoordinates_inverse_symmetric base hb
  have hzeroV : (0:E)∈V:=hdomain (mem_ball_self (by norm_num))
  obtain ⟨C⟩:=coordinateObjective_selfConcordant T hT f U ⟨D⟩
  have hsame (z : E) (hz : z∈V) : C.hessian z=coordinateDerivative T D.hessian z :=
    (C.gradient_derivative z hz).unique (coordinateObjective_gradient_hasFDerivAt T hT f U D z hz)
  have hzero : C.hessian 0=ContinuousLinearMap.id ℝ E := by
    rw [hsame 0 hzeroV]
    exact coordinateDerivative_metric_zero base hb D.hessian hH
  have hLip:=standardSelfConcordant_hessian_lipschitz (coordinateObjective T f) V C hzeroV hzero
    (R:=1/8) (by norm_num) hdomain
  have hLip4 : LipschitzOnWith (4:ℝ≥0) C.hessian (ball 0 (1/8)):=hLip.weaken (by norm_num)
  have hsmall : closedBall (0:E) (1/64)⊆ball 0 (1/8) := by
    intro z hz
    rw [mem_closedBall,dist_zero_right] at hz
    rw [mem_ball,dist_zero_right]
    linarith
  have hCLip : LipschitzOnWith (4:ℝ≥0) (coordinateDerivative T D.hessian) (closedBall 0 (1/64)) := by
    intro x hx y hy
    have hh:=hLip4 (hsmall hx) (hsmall hy)
    rwa [hsame x (hdomain (hsmall hx)),hsame y (hdomain (hsmall hy))] at hh
  have hmem (z : E) (hz : ‖T z‖≤1/64) : z∈U := by
    have hh:=hdomain (hsmall (by simpa only [mem_closedBall,dist_zero_right] using hz))
    change T.symm (T z)∈U at hh
    simpa only [T.symm_apply_apply] using hh
  refine ⟨hT,by norm_num,hgzero,coordinateDerivative_metric_zero base hb D.hessian hH,
    by norm_num,hCLip,?_,?_⟩
  · intro z hz
    exact (D.differentiable.differentiableAt (D.open_domain.mem_nhds (hmem z hz))).hasGradientAt.hasFDerivAt
  · intro z hz
    exact D.gradient_derivative z (hmem z hz)

end
end krylov.Convergence
