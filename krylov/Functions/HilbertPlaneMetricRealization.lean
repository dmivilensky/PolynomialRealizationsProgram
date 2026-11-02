import krylov.Functions.HilbertPlaneSelfConcordant

/-!
Article: main_krylov, prop:Fcycle(iii), full-dimensional true metric ball.
Use: turn the genuine planar self-concordant sources into actual scalar
functions in the complete CG space. The full Hessian is positive, its root
is constructed from that actual Hessian, and its full metric ball projects
inside the certified planar ball. The sharp tensor budget is preserved.
Source: orthogonal Hessian energy and the actual positive-root square identity.
-/
namespace krylov.Functions
noncomputable section
open Set Metric Matrix krylov.Tensor.BinaryCubic krylov.Nonlinear krylov.Reference krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The genuine positive-root metric is exactly the actual Hessian energy.
Article: main_krylov, prop:Fcycle(iii), true metric comparison. -/
theorem trueMetric_norm_sq (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (v : EuclideanSpace ℝ (Fin n)) :
    ‖metricCoordinates base hb v‖^2=inner ℝ v (cgOperator base v) := by
  rw [←referenceMetricSize_eq_norm base hb v,referenceMetricSize,Real.sq_sqrt]
  by_cases hv : v=0
  · simp only [hv,map_zero,inner_zero_left,le_refl]
  · exact ((cgOperator_positive base hb).2 v hv).le

/-- Every genuine planar true-metric source lifts to the complete space,
with its actual minimum, full prescribed true-Hessian ball and exact budget.
Article: main_krylov, prop:Fcycle(iii). -/
theorem hilbertPlane_true_metric_realization
    (e h m : EuclideanSpace ℝ (Fin n)) (he : ‖e‖=1) (hh : ‖h‖=1)
    (heh : inner ℝ e h=0) (hm : hilbertPlaneProject e h m=0)
    (p r a α : ℝ) (ha : 0<a) (t : krylov.Tensor.BinaryCubic)
    (z : Plane) (hreal : PlanarTrueMetricRealization p r a α t z) :
    let x := hilbertPlaneEmbed e h z+m
    let τ := scaleBinaryCubic α t
    let b := physicalOperatorMatrix (hilbertPlaneHessian e h p r τ x)
    gradient (hilbertPlaneObjective e h m p r τ) x=0 ∧
    ∃ hb : b.PosDef,
      cgOperator b=fderiv ℝ (gradient (hilbertPlaneObjective e h m p r τ)) x ∧
      (∀ v : EuclideanSpace ℝ (Fin n), |τ.tensor.form (hilbertPlaneProject e h v)
        (hilbertPlaneProject e h v) (hilbertPlaneProject e h v)|≤2*a*‖metricCoordinates b hb v‖^3) ∧
      IsStandardSelfConcordantOn (hilbertPlaneObjective e h m p r τ)
        {y | ‖metricCoordinates b hb (y-x)‖<canonicalCubicRadius a} ∧
      IsMinOn (hilbertPlaneObjective e h m p r τ)
        {y | ‖metricCoordinates b hb (y-x)‖<canonicalCubicRadius a} x := by
  let bp := physicalOperatorMatrix (planeCubicHessian p r (scaleBinaryCubic α t) z)
  obtain ⟨hcritical,hbp,hHp,hbudget,hSC,hmin⟩ := hreal
  let τ := scaleBinaryCubic α t
  let x := hilbertPlaneEmbed e h z+m
  let Hp := planeCubicHessian p r τ z
  let Hx := hilbertPlaneHessian e h p r τ x
  let b := physicalOperatorMatrix Hx
  have hPx : hilbertPlaneProject e h x=z := by
    dsimp only [x]
    rw [map_add,hilbertPlaneProject_embed e h he hh heh,hm,add_zero]
  have hHp' : cgOperator bp=Hp := hHp.trans (planeCubicGradient_hasFDerivAt p r τ z).fderiv
  have hpp v : 0≤ inner ℝ v (Hp v) := by
    rw [←hHp']
    by_cases hv : v=0
    · simp only [hv,map_zero,inner_zero_left,le_refl]
    · exact ((cgOperator_positive bp hbp).2 v hv).le
  have hpos v (hv : v≠0) : 0 < inner ℝ v (Hx v) := by
    dsimp only [Hx]
    rw [hilbertPlaneHessian_energy e h he hh heh,hPx]
    by_cases hPv : hilbertPlaneProject e h v=0
    · simp only [hPv,map_zero,sub_zero,inner_zero_left,zero_add]
      exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv)
    · have hpositive : 0< inner ℝ (hilbertPlaneProject e h v) (Hp (hilbertPlaneProject e h v)) := by
        rw [←hHp']
        exact (cgOperator_positive bp hbp).2 _ hPv
      exact hpositive.trans_le (le_add_of_nonneg_right (sq_nonneg _))
  have hb : b.PosDef := physicalOperatorMatrix_posDef Hx (hilbertPlaneHessian_symmetric e h p r τ x) hpos
  let Sp := metricCoordinates bp hbp
  let S := metricCoordinates b hb
  have hSp v : ‖Sp v‖^2=inner ℝ v (Hp v) := by rw [trueMetric_norm_sq,hHp']
  have hS v : ‖S v‖^2=inner ℝ v (Hx v) := by rw [trueMetric_norm_sq,physicalOperatorMatrix_operator]
  have hproject v : ‖Sp (hilbertPlaneProject e h v)‖≤‖S v‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [hSp,hS]
    dsimp only [Hx,Hp]
    rw [hilbertPlaneHessian_energy e h he hh heh,hPx]
    exact le_add_of_nonneg_right (sq_nonneg _)
  let R := canonicalCubicRadius a
  let V : Set (EuclideanSpace ℝ (Fin n)) := {y | ‖S (y-x)‖<R}
  let U := planarTrueMetricBall Sp z R
  have hVU y (hy : y∈V) : hilbertPlaneProject e h y∈U := by
    have heq : hilbertPlaneProject e h (y-x)=hilbertPlaneProject e h y-z := by rw [map_sub,hPx]
    change ‖Sp (hilbertPlaneProject e h y-z)‖<R
    rw [←heq]
    exact (hproject (y-x)).trans_lt hy
  have hVo : IsOpen V := isOpen_lt (by fun_prop) continuous_const
  have hVc : Convex ℝ V := by
    have hc := ((convex_ball (0 : EuclideanSpace ℝ (Fin n)) R).linear_preimage S.toLinearMap).translate_preimage_left (-x)
    change Convex ℝ {y | dist (S (y+ -x)) 0<R} at hc
    simpa only [V,dist_zero_right,sub_eq_add_neg] using hc
  refine ⟨hilbertPlaneGradient_critical e h m he hh heh hm p r τ z hcritical,hb,?_,?_,?_,?_⟩
  · rw [physicalOperatorMatrix_operator]
    exact (hilbertPlaneGradient_hasFDerivAt e h m p r τ x).fderiv.symm
  · intro v
    exact (hbudget (hilbertPlaneProject e h v)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hproject v) 3) (by positivity))
  · exact hilbertPlaneObjective_selfConcordant e h m he hh heh p r τ U hSC V hVo hVc hVU
  · exact hilbertPlaneObjective_isMinOn e h m he hh heh hm p r τ U z hmin V hVU

end
end krylov.Functions
