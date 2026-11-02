import krylov.Functions.PlanarSelfConcordant
import krylov.Functions.PlanarShrinkMargins
import krylov.Functions.PlanarCubicMinima
import krylov.Functions.FCOwnCanonical

/-!
Article: main_krylov, prop:Fcycle(iii), exact true-minimizer SC normalization.
Use: the linear tensor shrink pays the actual quadratic perturbation and
true Hessian distortion while preserving both the prescribed tensor budget
and the full printed self-concordant radius in the true minimizer metric.
Source: actual cubic derivatives, genuine criticality, positive metric-root
construction and the explicit scalar shrink margins.
-/
namespace krylov.Functions
noncomputable section
open Set Metric Matrix krylov.Tensor.BinaryCubic krylov.Nonlinear krylov.Reference krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator

/-- The actual true-minimizer metric ball, with its genuine positive root.
Article: main_krylov, prop:Fcycle(iii). -/
def planarTrueMetricBall (S : Plane ≃L[ℝ] Plane) (x : Plane) (R : ℝ) : Set Plane :=
  {y | ‖S (y-x)‖<R}

set_option maxHeartbeats 1000000 in
/-- A real critical point of the actual shrunk scalar cubic is its genuine
minimizer on the full printed true-Hessian metric ball. The actual third
derivative obeys exactly the prescribed 2a budget in that true metric and
the function is standard self-concordant on that complete ball.
Article: main_krylov, prop:Fcycle(iii), actual SC shrink realization. -/
theorem planeCubic_shrunk_true_metric
    (p r a M C : ℝ) (hp : 0≤p) (ha : 0<a) (ha₁ : a<1) (hM : 0≤M)
    {t : krylov.Tensor.BinaryCubic} (ht : t.InBall)
    (hC : 2*a*(‖planeTerminalOperator r t‖+M)≤C) (hq : 0<1-C*p)
    (x : Plane) (hx : ‖x-planeOfPair (p,r*p)‖≤M*p)
    (hcritical : gradient (planeCubicObjective p r (scaleBinaryCubic (2*a*(1-C*p)^3) t)) x=0) :
    let α := 2*a*(1-C*p)^3
    let b := physicalOperatorMatrix (planeCubicHessian p r (scaleBinaryCubic α t) x)
    ∃ hb : b.PosDef,
      cgOperator b=fderiv ℝ (gradient (planeCubicObjective p r (scaleBinaryCubic α t))) x ∧
      (∀ v : Plane, |(scaleBinaryCubic α t).tensor.form v v v|≤
        2*a*‖metricCoordinates b hb v‖^3) ∧
      IsStandardSelfConcordantOn (planeCubicObjective p r (scaleBinaryCubic α t))
        (planarTrueMetricBall (metricCoordinates b hb) x (canonicalCubicRadius a)) ∧
      IsMinOn (planeCubicObjective p r (scaleBinaryCubic α t))
        (planarTrueMetricBall (metricCoordinates b hb) x (canonicalCubicRadius a)) x := by
  let q := 1-C*p
  let α := 2*a*q^3
  let Hx := planeCubicHessian p r (scaleBinaryCubic α t) x
  let b := physicalOperatorMatrix Hx
  have hα : 0<α := by dsimp only [α]; positivity
  have hC₀ : 0≤C := (by positivity : 0≤2*a*(‖planeTerminalOperator r t‖+M)).trans hC
  have hq₁ : q≤1 := by dsimp only [q]; nlinarith only [mul_nonneg hC₀ hp]
  have hpoint := shrink_true_metric_margin a ‖planeTerminalOperator r t‖ M C p ha.le (norm_nonneg _) hM hp hC hq
  have hstar v : q^2*‖v‖^2≤ inner ℝ v (Hx v) := by
    have hscalar : q^2≤1-α*p*‖planeTerminalOperator r t‖-α*‖x-planeOfPair (p,r*p)‖ := by
      change q^2≤1-α*p*‖planeTerminalOperator r t‖-α*(M*p) at hpoint
      nlinarith only [hpoint,mul_le_mul_of_nonneg_left hx hα.le]
    exact (mul_le_mul_of_nonneg_right hscalar (sq_nonneg _)).trans
      (planeCubicHessian_scaled_lower p r α hp hα.le ht x v)
  have hpos v (hv : v≠0) : 0 < inner ℝ v (Hx v) :=
    (by have hn := norm_pos_iff.mpr hv; positivity : 0<q^2*‖v‖^2).trans_le (hstar v)
  have hb : b.PosDef := physicalOperatorMatrix_posDef Hx (planeCubicHessian_symmetric _ _ _ _) hpos
  let S := metricCoordinates b hb
  have hSsq v : ‖S v‖^2=inner ℝ v (Hx v) := by
    have hs : (cgOperator (metricRoot b)).toLinearMap.IsSymmetric :=
      Matrix.isSymmetric_toEuclideanLin_iff.mpr (metricRoot_isSymm b)
    have hh : cgOperator (metricRoot b) (cgOperator (metricRoot b) v)=cgOperator b v := by
      simp only [cgOperator,←mul_apply_eq_comp,←map_mul,metricRoot_square b hb]
    rw [←real_inner_self_eq_norm_sq]
    change inner ℝ (cgOperator (metricRoot b) v) (cgOperator (metricRoot b) v)=_
    have hself := hs v (cgOperator (metricRoot b) v)
    change inner ℝ (cgOperator (metricRoot b) v) (cgOperator (metricRoot b) v)=
      inner ℝ v (cgOperator (metricRoot b) (cgOperator (metricRoot b) v)) at hself
    rw [hself,hh,physicalOperatorMatrix_operator]
  have hSlower v : q*‖v‖≤‖S v‖ := by
    apply (sq_le_sq₀ (by positivity : 0≤q*‖v‖) (norm_nonneg _)).mp
    rw [mul_pow,hSsq]
    exact hstar v
  let R := canonicalCubicRadius a
  let s := Real.sqrt (1-2*a*R)
  have hR : 0<R := canonicalCubicRadius_pos ha ha₁
  have hmargin : 0<1-2*a*R := by
    rw [show R=canonicalCubicRadius a from rfl,canonicalCubicRadius_margin ha]
    exact Real.rpow_pos_of_pos ha _
  have hs : 0<s := Real.sqrt_pos.mpr hmargin
  have hs₃ : s^3=a := canonicalCubicRadius_compat ha
  have hRdef : 2*a*R=1-s^2 := by
    dsimp only [s]
    rw [Real.sq_sqrt hmargin.le]
    ring
  let U := planarTrueMetricBall S x R
  have hUo : IsOpen U := isOpen_lt (by fun_prop) continuous_const
  have hUc : Convex ℝ U := by
    have hh := ((convex_ball (0 : Plane) R).linear_preimage S.toLinearMap).translate_preimage_left (-x)
    change Convex ℝ {y | dist (S (y+ -x)) 0<R} at hh
    simpa only [U,planarTrueMetricBall,dist_zero_right,sub_eq_add_neg] using hh
  have hscalar z (hz : z∈U) : (s*q)^2≤1-α*p*‖planeTerminalOperator r t‖-α*‖z-planeOfPair (p,r*p)‖ := by
    have hz' : ‖S (z-x)‖<R := hz
    have hdist : ‖z-x‖≤R/q := by
      apply (le_div_iff₀ hq).mpr
      nlinarith only [hSlower (z-x),hz']
    have hnorm : ‖z-planeOfPair (p,r*p)‖≤R/q+M*p := by
      calc
        _ = ‖(z-x)+(x-planeOfPair (p,r*p))‖ := by congr 1; abel
        _ ≤ ‖z-x‖+‖x-planeOfPair (p,r*p)‖ := norm_add_le _ _
        _ ≤ R/q+M*p := add_le_add hdist hx
    have hh := shrink_sc_radius_margin a ‖planeTerminalOperator r t‖ M C p R s
      ha.le (norm_nonneg _) hM hp hC hq hRdef
    change (s*q)^2≤1-α*p*‖planeTerminalOperator r t‖-α*(R/q+M*p) at hh
    nlinarith only [hh,mul_le_mul_of_nonneg_left hnorm hα.le]
  have hSC : IsStandardSelfConcordantOn (planeCubicObjective p r (scaleBinaryCubic α t)) U := by
    apply planeCubic_scaled_selfConcordant_margin p r α (s*q) hp hα.le (mul_pos hs hq) _ ht U hUo hUc hscalar
    rw [mul_pow,hs₃]
    exact le_of_eq (by dsimp only [α]; ring)
  refine ⟨hb,?_,?_,hSC,?_⟩
  · rw [physicalOperatorMatrix_operator]
    exact (planeCubicGradient_hasFDerivAt p r (scaleBinaryCubic α t) x).fderiv.symm
  · intro v
    rw [scaleBinaryCubic_tensor_apply,abs_mul,abs_of_nonneg hα.le]
    have hv := mul_le_mul_of_nonneg_left (tensor_bound ht v v v) hα.le
    have hp₃ := pow_le_pow_left₀ (by positivity : 0≤q*‖v‖) (hSlower v) 3
    calc
      _ ≤ α*(‖v‖*‖v‖*‖v‖) := hv
      _ = 2*a*(q*‖v‖)^3 := by dsimp only [α]; ring
      _ ≤ 2*a*‖S v‖^3 := mul_le_mul_of_nonneg_left hp₃ (by positivity)
  · have hxin : x∈U := by
      change ‖S (x-x)‖<R
      simpa only [sub_self,map_zero,norm_zero] using hR
    apply planeCubicObjective_isMinOn p r ((s*q)^2) (sq_nonneg _) _ U x hxin hcritical
    intro z hz v
    exact (mul_le_mul_of_nonneg_right (hscalar z hz) (sq_nonneg _)).trans
      (planeCubicHessian_scaled_lower p r α hp hα.le ht z v)

end
end krylov.Functions
