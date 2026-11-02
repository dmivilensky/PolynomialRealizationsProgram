import krylov.Functions.RFCFSelfConcordantTensor
import krylov.Nonlinear.SelfConcordantCoordinates

/-!
Article: main_krylov, prop:Fcycle(iii), genuine physical metric pullback.
Use: transport an actual scalar self-concordant realization through the
constructed positive root of any positive physical reference matrix, with
its true minimum, Hessian and full true-Hessian metric ball preserved.
Source: the actual scalar/gradient/Hessian chain rules, standard mixed
self-concordance coordinate invariance and genuine metric-energy identities.
-/
namespace krylov.Functions
noncomputable section
open Set Metric Matrix Topology krylov.Nonlinear krylov.Reference krylov.Secant krylov.Variation
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {n : ℕ}

/-- A genuine scalar standard-self-concordant function stays standard self-concordant under an actual symmetric inverse linear coordinate equivalence.
Article: main_krylov, prop:Fcycle(iii), complete scalar coordinate invariance. -/
theorem coordinateObjective_selfConcordant (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric) (f : E → ℝ) (U : Set E)
    (hsc : IsStandardSelfConcordantOn f U) :
    IsStandardSelfConcordantOn (coordinateObjective T f) (T.symm ⁻¹' U) := by
  obtain ⟨D⟩ := hsc
  let V := T.symm ⁻¹' U
  have hVo : IsOpen V := D.open_domain.preimage T.symm.continuous
  have hg y (hy : y∈V) : gradient (coordinateObjective T f) y=coordinateGradient T (gradient f) y :=
    gradient_coordinateObjective T hT f y
      (D.differentiable.differentiableAt (D.open_domain.mem_nhds hy))
  have he y (a b : E) : inner ℝ a (coordinateDerivative T D.hessian y b)=
      inner ℝ (T.symm a) (D.hessian (T.symm y) (T.symm b)) := by
    change inner ℝ a (T.symm (D.hessian (T.symm y) (T.symm b)))=_
    exact (hT a _).symm
  refine ⟨{
    open_domain := hVo
    convex_domain := D.convex_domain.linear_preimage T.symm.toLinearMap
    differentiable := ?_
    hessian := coordinateDerivative T D.hessian
    variation := coordinateHessianVariation T D.variation
    gradient_derivative := ?_
    hessian_derivative := fun y hy=>coordinateDerivative_hasFDerivAt T D.hessian D.variation y
      (D.hessian_derivative (T.symm y) hy)
    variation_continuous := ?_
    hessian_symmetric := ?_
    hessian_nonnegative := ?_
    mixed := fun y hy=>coordinate_mixed_selfConcordance T hT D.hessian D.variation y (D.mixed _ hy)
  }⟩
  · intro y hy
    exact ((D.differentiable.differentiableAt (D.open_domain.mem_nhds hy)).comp y
      T.symm.differentiableAt).differentiableWithinAt
  · intro y hy
    have hd := coordinateGradient_hasFDerivAt T (gradient f) D.hessian y (D.gradient_derivative _ hy)
    have hev : gradient (coordinateObjective T f) =ᶠ[𝓝 y] coordinateGradient T (gradient f) :=
      Filter.eventually_of_mem (hVo.mem_nhds hy) (fun z hz=>hg z hz)
    exact hd.congr_of_eventuallyEq hev
  · intro y hy
    have hc : ContinuousAt (fun z=>D.variation (T.symm z)) y :=
      (D.variation_continuous.continuousAt (D.open_domain.mem_nhds hy)).comp T.symm.continuousAt
    have hc' := hc.clm_comp (continuousAt_const : ContinuousAt (fun _ : E=>T.symm.toContinuousLinearMap) y)
    exact (((coordinateCongruence T).postcomp E).continuous.continuousAt.comp hc').continuousWithinAt
  · intro y hy a b
    change inner ℝ (coordinateDerivative T D.hessian y a) b=inner ℝ a (coordinateDerivative T D.hessian y b)
    rw [real_inner_comm,he,he]
    exact (real_inner_comm _ _).trans (D.hessian_symmetric _ hy (T.symm a) (T.symm b))
  · intro y hy v
    rw [he]
    exact D.hessian_nonnegative _ hy (T.symm v)

omit [CompleteSpace E] in
/-- A genuine scalar minimum transports exactly through the actual coordinate equivalence.
Article: main_krylov, prop:Fcycle(iii), true physical minimum. -/
theorem coordinateObjective_isMinOn (T : E ≃L[ℝ] E) (f : E → ℝ) (U : Set E)
    (x : E) (hx : IsMinOn f U x) :
    IsMinOn (coordinateObjective T f) (T.symm ⁻¹' U) (T x) := by
  intro y hy
  change coordinateObjective T f (T x)≤coordinateObjective T f y
  rw [coordinateObjective_apply]
  exact hx hy

/-- The forward positive-root coordinate map is genuinely self-adjoint.
Article: main_krylov, prop:Fcycle(iii), actual physical Hessian pullback. -/
theorem metricPullback_symmetric (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) :
    (metricCoordinates base hb).toContinuousLinearMap.IsSymmetric := by
  apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
  exact metricRoot_isSymm base

/-- The actual physical scalar pullback by the original positive metric root.
Article: main_krylov, prop:Fcycle(iii), f_physical(x)=f_canonical(A^(1/2)x). -/
def metricPullbackObjective (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  f (metricCoordinates base hb x)

/-- The physical positive-root pullback preserves full scalar standard self-concordance on the entire exact pulled-back domain.
Article: main_krylov, prop:Fcycle(iii), true physical source realization. -/
theorem metricPullbackObjective_selfConcordant
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hsc : IsStandardSelfConcordantOn f U) :
    IsStandardSelfConcordantOn (metricPullbackObjective base hb f) ((metricCoordinates base hb) ⁻¹' U) :=
  coordinateObjective_selfConcordant (metricCoordinates base hb).symm (metricPullback_symmetric base hb) f U hsc

/-- The physical scalar pullback has precisely the inverse-transported true minimum on the exact full domain.
Article: main_krylov, prop:Fcycle(iii), actual minimum after physical realization. -/
theorem metricPullbackObjective_isMinOn
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) (hx : IsMinOn f U x) :
    IsMinOn (metricPullbackObjective base hb f) ((metricCoordinates base hb) ⁻¹' U)
      ((metricCoordinates base hb).symm x) :=
  coordinateObjective_isMinOn (metricCoordinates base hb).symm f U x hx

/-- The actual transported scalar gradient has the genuine transported Hessian at every interior source point.
Article: main_krylov, prop:Fcycle(iii), actual physical Hessian identity. -/
theorem coordinateObjective_gradient_hasFDerivAt (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric) (f : E → ℝ) (U : Set E)
    (D : StandardSelfConcordantData f U) (y : E) (hy : T.symm y∈U) :
    HasFDerivAt (gradient (coordinateObjective T f)) (coordinateDerivative T D.hessian y) y := by
  have hVo : IsOpen (T.symm ⁻¹' U) := D.open_domain.preimage T.symm.continuous
  have hev : gradient (coordinateObjective T f) =ᶠ[𝓝 y] coordinateGradient T (gradient f) := by
    filter_upwards [hVo.mem_nhds hy] with z hz
    exact gradient_coordinateObjective T hT f z
      (D.differentiable.differentiableAt (D.open_domain.mem_nhds hz))
  exact (coordinateGradient_hasFDerivAt T (gradient f) D.hessian y (D.gradient_derivative _ hy)).congr_of_eventuallyEq hev

/-- Genuine positive-root congruence transports every positive true minimizer Hessian to a positive physical Hessian.
Article: main_krylov, prop:Fcycle(iii), actual true metric construction. -/
theorem metricPullbackMatrix_posDef
    (base b : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef) (hb : b.PosDef) :
    (metricRoot base*b*metricRoot base).PosDef := by
  have hinj : Function.Injective (metricRoot base).mulVec :=
    Matrix.mulVec_injective_of_det_ne_zero (isUnit_iff_ne_zero.mp (metricRoot_det_unit base hbase))
  simpa only [conjTranspose_eq_transpose_of_trivial,(metricRoot_isSymm base).eq] using
    hb.conjTranspose_mul_mul_same (B:=metricRoot base) hinj

/-- The genuine transported true-Hessian metric is exactly the original true metric after the actual root coordinate map.
Article: main_krylov, prop:Fcycle(iii), no metric-radius loss. -/
theorem metricPullback_true_metric_norm
    (base b : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef) (hb : b.PosDef)
    (hP : (metricRoot base*b*metricRoot base).PosDef)
    (v : EuclideanSpace ℝ (Fin n)) :
    ‖metricCoordinates (metricRoot base*b*metricRoot base) hP v‖=
      ‖metricCoordinates b hb (metricCoordinates base hbase v)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [←physical_energy_metric_norm _ hP,←physical_energy_metric_norm b hb]
  exact metric_drift_pairing base b v v

/-- The full actual true-minimizer metric ball pulls back exactly, retaining its centre and complete prescribed radius.
Article: main_krylov, prop:Fcycle(iii), exact physical source domain. -/
theorem metricPullback_true_metric_ball
    (base b : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef) (hb : b.PosDef)
    (hP : (metricRoot base*b*metricRoot base).PosDef)
    (x : EuclideanSpace ℝ (Fin n)) (R : ℝ) :
    {y | ‖metricCoordinates (metricRoot base*b*metricRoot base) hP
      (y-(metricCoordinates base hbase).symm x)‖<R}=
      (metricCoordinates base hbase) ⁻¹' {z | ‖metricCoordinates b hb (z-x)‖<R} := by
  ext y
  change ‖metricCoordinates (metricRoot base*b*metricRoot base) hP
    (y-(metricCoordinates base hbase).symm x)‖<R ↔
    ‖metricCoordinates b hb (metricCoordinates base hbase y-x)‖<R
  rw [metricPullback_true_metric_norm base b hbase hb hP]
  simp only [map_sub,ContinuousLinearEquiv.apply_symm_apply]

/-- An actual scalar third-direction budget is preserved exactly in the genuine physical true-Hessian metric.
Article: main_krylov, prop:Fcycle(iii), original prescribed canonical tensor budget. -/
theorem metricPullback_true_tensor_budget
    (base b : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef) (hb : b.PosDef)
    (hP : (metricRoot base*b*metricRoot base).PosDef)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (B : ℝ)
    (hF : ∀ v,|F v|≤B*‖metricCoordinates b hb v‖^3) :
    ∀ v,|F (metricCoordinates base hbase v)|≤B*‖metricCoordinates (metricRoot base*b*metricRoot base) hP v‖^3 := by
  intro v
  rw [metricPullback_true_metric_norm base b hbase hb hP]
  exact hF _

/-- A genuine complete true-metric scalar realization becomes a genuine physical realization at any prescribed positive reference metric, with no loss in tensor budget or radius.
Article: main_krylov, prop:Fcycle(iii), actual physical full-dimensional cubic realization.
The true physical minimum, actual Riesz-gradient Hessian, full standard
self-concordant domain and original directional tensor bound are conclusions. -/
theorem metricPullback_true_metric_realization
    (base b : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef) (hb : b.PosDef)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (R B : ℝ) (hR : 0<R) (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hcritical : gradient f x=0) (hH : cgOperator b=fderiv ℝ (gradient f) x)
    (hbudget : ∀ v,|F v|≤B*‖metricCoordinates b hb v‖^3)
    (hsc : IsStandardSelfConcordantOn f {z | ‖metricCoordinates b hb (z-x)‖<R})
    (hmin : IsMinOn f {z | ‖metricCoordinates b hb (z-x)‖<R} x) :
    let P := metricRoot base*b*metricRoot base
    let y := (metricCoordinates base hbase).symm x
    gradient (metricPullbackObjective base hbase f) y=0 ∧
    ∃ hP : P.PosDef,
      cgOperator P=fderiv ℝ (gradient (metricPullbackObjective base hbase f)) y ∧
      (∀ v,|F (metricCoordinates base hbase v)|≤B*‖metricCoordinates P hP v‖^3) ∧
      IsStandardSelfConcordantOn (metricPullbackObjective base hbase f)
        {z | ‖metricCoordinates P hP (z-y)‖<R} ∧
      IsMinOn (metricPullbackObjective base hbase f) {z | ‖metricCoordinates P hP (z-y)‖<R} y := by
  let S := metricCoordinates base hbase
  let U : Set (EuclideanSpace ℝ (Fin n)) := {z | ‖metricCoordinates b hb (z-x)‖<R}
  let P := metricRoot base*b*metricRoot base
  let y := S.symm x
  obtain ⟨D⟩ := hsc
  have hx : x∈U := by simpa only [U,Set.mem_ofPred_eq,sub_self,map_zero,norm_zero] using hR
  have hy : S y∈U := by simpa only [y,S.apply_symm_apply] using hx
  have hsym := metricPullback_symmetric base hbase
  have hgrad := gradient_coordinateObjective S.symm hsym f y
    (D.differentiable.differentiableAt (D.open_domain.mem_nhds hy))
  have hcrit : gradient (metricPullbackObjective base hbase f) y=0 := by
    change gradient (coordinateObjective S.symm f) y=0
    rw [hgrad]
    change S (gradient f (S y))=0
    rw [show S y=x from S.apply_symm_apply x,hcritical,map_zero]
  have hDc : D.hessian x=cgOperator b := (D.gradient_derivative x hx).fderiv.symm.trans hH.symm
  have hder := coordinateObjective_gradient_hasFDerivAt S.symm hsym f U D y hy
  have hcong : coordinateDerivative S.symm D.hessian y=cgOperator P := by
    apply ContinuousLinearMap.ext
    intro v
    change S (D.hessian (S y) (S v))=cgOperator P v
    rw [show S y=x from S.apply_symm_apply x,hDc]
    simp only [S,metricCoordinates_apply,P,cgOperator,map_mul,mul_apply_eq_comp]
  rw [hcong] at hder
  have hP : P.PosDef := metricPullbackMatrix_posDef base b hbase hb
  refine ⟨hcrit,hP,hder.fderiv.symm,metricPullback_true_tensor_budget base b hbase hb hP F B hbudget,?_,?_⟩
  · rw [metricPullback_true_metric_ball base b hbase hb hP x R]
    exact metricPullbackObjective_selfConcordant base hbase f U ⟨D⟩
  · rw [metricPullback_true_metric_ball base b hbase hb hP x R]
    exact metricPullbackObjective_isMinOn base hbase f U x hmin

end
end krylov.Functions
