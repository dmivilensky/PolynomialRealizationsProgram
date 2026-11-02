import krylov.Functions.ReferencePlaneCriticalNormalization

/-!
Article: main_krylov, prop:Fcycle(iii), sharp original full-reference sources.
Use: instantiate the attained information fibre in the literal scalar family
at ε g, preserving its true minima, full true-Hessian SC balls and sharp
common-output error lower bound. Source: genuine full-space realization,
exact original-source scaling and the actual CG energy dictionary.
-/
namespace krylov.Functions
noncomputable section
open Matrix Set krylov.Reference krylov.Secant krylov.Nonlinear krylov.Tensor.BinaryCubic
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- A complete actual source certificate for the literal original scalar
family. Its Hessian and metric are those at the genuine critical point.
Article: main_krylov, prop:Fcycle(iii). -/
def ReferencePlaneTrueMetricRealization (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (ε a : ℝ) (t : krylov.Tensor.BinaryCubic)
    (z : EuclideanSpace ℝ (Fin n)) : Prop :=
  let S := metricCoordinates A hA
  let f := referencePlaneCubicObjective A hA (ε • g) t
  let P := metricHilbertPlaneTrueHessian A (referencePlaneFirst A g) (referencePlaneLast A hA g)
    (ε*‖canonicalCGStep A g 0‖) (referencePlaneRatio A hA g) t z
  let y := S.symm z
  gradient f y=0 ∧ ∃ hP : P.PosDef,
    cgOperator P=fderiv ℝ (gradient f) y ∧
    (∀ v : EuclideanSpace ℝ (Fin n), |t.tensor.form
      (hilbertPlaneProject (referencePlaneFirst A g) (referencePlaneLast A hA g) (S v))
      (hilbertPlaneProject (referencePlaneFirst A g) (referencePlaneLast A hA g) (S v))
      (hilbertPlaneProject (referencePlaneFirst A g) (referencePlaneLast A hA g) (S v))|≤
      2*a*‖metricCoordinates P hP v‖^3) ∧
    IsStandardSelfConcordantOn f {x | ‖metricCoordinates P hP (x-y)‖<canonicalCubicRadius a} ∧
    IsMinOn f {x | ‖metricCoordinates P hP (x-y)‖<canonicalCubicRadius a} y

/-- The physical realization certificate is exactly the certificate of the
literal ε-scaled original scalar source. Article: prop:Fcycle(iii). -/
theorem referencePlane_true_metric_realization
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) {ε a : ℝ} (hε : 0<ε) (ha : 0<a) (ha₁ : a<1)
    (t : krylov.Tensor.BinaryCubic) (z : EuclideanSpace ℝ (Fin n))
    (hr : HilbertPlaneTrueMetricRealization (referencePlaneFirst A g) (referencePlaneLast A hA g)
      (ε • referencePlaneComplement A hA g) (ε*‖canonicalCGStep A g 0‖) (referencePlaneRatio A hA g) a t z) :
    ReferencePlaneTrueMetricRealization A hA g ε a t z := by
  have hp := metricHilbertPlane_true_metric_realization A hA _ _ _ _ _ a ha ha₁ t z hr
  simpa only [ReferencePlaneTrueMetricRealization,MetricHilbertPlaneTrueMetricRealization,
    referencePlaneCubicObjective_positive_scalar A hA g hε] using hp

set_option maxHeartbeats 800000 in
/-- Attained sharp fibres are genuine original full-reference scalar sources,
with true SC minima, actual initial gradients, independently controlled true
metrics and normalized minimizer displacements. Every unrestricted common
output has the printed cubic reference lower bound with quartic remainder.
Article: main_krylov, prop:Fcycle(iii). -/
theorem referencePlane_sharp_actual_sources
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g)
    (a : ℝ) (ha : 0<a) (ha₁ : a<1) :
    let e := referencePlaneFirst A g
    let h := referencePlaneLast A hA g
    let p₀ := ‖canonicalCGStep A g 0‖
    let r := referencePlaneRatio A hA g
    let m := referencePlaneComplement A hA g
    ∃ t u : krylov.Tensor.BinaryCubic, Chord r t u ∧ chordValue r t u=fibreMinimax r ∧
    ∃ ep C M E : ℝ, 0<ep ∧ 0<C ∧ 0<M ∧ 0<E ∧
      ∀ ε : ℝ, 0<ε → ε<ep →
      let p := ε*p₀
      let α := 2*a*(1-C*p)^3
      let τ := scaleBinaryCubic α t
      let υ := scaleBinaryCubic α u
      0<α ∧ α≤2*a ∧ observe r τ=observe r υ ∧
      gradient (referencePlaneCubicObjective A hA (ε • g) τ) 0=ε • g ∧
      gradient (referencePlaneCubicObjective A hA (ε • g) υ) 0=ε • g ∧
      ∃ z w : Plane,
        ‖z-planeOfPair (p,r*p)‖≤M*p^2 ∧ ‖w-planeOfPair (p,r*p)‖≤M*p^2 ∧
        let zf := hilbertPlaneEmbed e h z+ε • m
        let wf := hilbertPlaneEmbed e h w+ε • m
        ReferencePlaneTrueMetricRealization A hA g ε a τ zf ∧
        ReferencePlaneTrueMetricRealization A hA g ε a υ wf ∧
        ‖metricHilbertPlaneTrueHessian A e h p r τ zf-A‖≤
          ‖(metricCoordinates A hA).toContinuousLinearMap‖^2*C*p₀*ε ∧
        ‖metricHilbertPlaneTrueHessian A e h p r υ wf-A‖≤
          ‖(metricCoordinates A hA).toContinuousLinearMap‖^2*C*p₀*ε ∧
        ‖(-ε⁻¹) • (metricCoordinates A hA).symm zf-referencePlaneInitialError A hA g‖≤
          ‖(metricCoordinates A hA).symm.toContinuousLinearMap‖*M*p₀^2*ε ∧
        ‖(-ε⁻¹) • (metricCoordinates A hA).symm wf-referencePlaneInitialError A hA g‖≤
          ‖(metricCoordinates A hA).symm.toContinuousLinearMap‖*M*p₀^2*ε ∧
        ∀ x : EuclideanSpace ℝ (Fin n),
          a^2*referenceFibreCoefficient A g (referenceAtomCount A hA g-1)*ε^3-E*ε^4≤
            max (metricHilbertPlaneMetricError A hA e h p r τ zf x)
              (metricHilbertPlaneMetricError A hA e h p r υ wf x) := by
  dsimp only
  let e := referencePlaneFirst A g
  let h := referencePlaneLast A hA g
  let p₀ := ‖canonicalCGStep A g 0‖
  let r := referencePlaneRatio A hA g
  let m := referencePlaneComplement A hA g
  obtain ⟨hp₀,hr,he,hh,heh,_,_⟩ := referencePlane_sample_lines A hA g hN
  change 0<p₀ at hp₀
  change 0<r at hr
  obtain ⟨t,u,hch,hatt,ep,C,M,E,hep,hC,hM,hE,hs⟩ :=
    hilbertPlane_sharp_true_metric_sources e h he hh heh r a hr ha ha₁
  refine ⟨t,u,hch,hatt,ep/p₀,C,M,E*p₀^4,div_pos hep hp₀,hC,hM,mul_pos hE (pow_pos hp₀ 4),?_⟩
  intro ε hε heps
  have hp : 0<ε*p₀ := mul_pos hε hp₀
  have hpe : ε*p₀<ep := (lt_div_iff₀ hp₀).mp heps
  have hm : hilbertPlaneProject e h (ε • m)=0 := by
    rw [map_smul,referencePlaneComplement_project A hA g hN,smul_zero]
  obtain ⟨hα,hαU,hobs,z,w,hz,hw,hzt,hwu,hdz,hdw,hlower⟩ := hs (ε*p₀) hp hpe (ε • m) hm
  let α := 2*a*(1-C*(ε*p₀))^3
  let τ := scaleBinaryCubic α t
  let υ := scaleBinaryCubic α u
  let zf := hilbertPlaneEmbed e h z+ε • m
  let wf := hilbertPlaneEmbed e h w+ε • m
  refine ⟨hα,hαU,hobs,referencePlaneCubicObjective_initial_gradient A hA g hN hε τ,
    referencePlaneCubicObjective_initial_gradient A hA g hN hε υ,z,w,hz,hw,
    referencePlane_true_metric_realization A hA g hε ha ha₁ τ zf hzt,
    referencePlane_true_metric_realization A hA g hε ha ha₁ υ wf hwu,?_,?_,
    referencePlane_normalized_initial_error A hA g hN hε z hz,
    referencePlane_normalized_initial_error A hA g hN hε w hw,?_⟩
  · have hb := metricCongruence_physicalMatrix_drift A hA (hilbertPlaneHessian e h (ε*p₀) r τ zf)
    rw [metricCongruence_physicalMatrix] at hb
    exact hb.trans ((mul_le_mul_of_nonneg_left hdz (sq_nonneg _)).trans_eq (by ring))
  · have hb := metricCongruence_physicalMatrix_drift A hA (hilbertPlaneHessian e h (ε*p₀) r υ wf)
    rw [metricCongruence_physicalMatrix] at hb
    exact hb.trans ((mul_le_mul_of_nonneg_left hdw (sq_nonneg _)).trans_eq (by ring))
  · intro x
    have hb := metricHilbertPlane_common_error_lower A hA e h (ε • m) (ε*p₀) r a τ υ zf wf
      hzt hwu _ hlower x
    convert! hb using 1
    rw [←referencePlane_coefficient A hA g hN]
    dsimp only [p₀,r]
    ring

end
end krylov.Functions
