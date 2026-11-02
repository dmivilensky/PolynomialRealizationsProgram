import krylov.Functions.HilbertPlaneBounds
import krylov.Functions.TrueMetricGradientBound
import krylov.Functions.PlanarSharpShrink

/-!
Article: main_krylov, prop:Fcycle(iii), complete-space true-error sharp sources.
Use: realize an attained exact value-information fibre by full-dimensional
actual scalar functions, on their full true-Hessian SC balls, and derive the
sharp cubic lower bound on the actual error of every common output.
Source: actual planar shrink, orthogonal lift, genuine global gradient Taylor
bounds and the derived unrestricted-output error comparison.
-/
namespace krylov.Functions
noncomputable section
open Set Metric Matrix krylov.Tensor.BinaryCubic krylov.Nonlinear krylov.Reference krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- True error in the actual minimizer Hessian, written as its quadratic form.
The realized Hessian is positive and this equals its constructed root norm.
Article: main_krylov, prop:Fcycle(iii). -/
def hilbertPlaneMetricError (e h : EuclideanSpace ℝ (Fin n)) (p r : ℝ)
    (t : krylov.Tensor.BinaryCubic) (z x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  referenceMetricSize (physicalOperatorMatrix (hilbertPlaneHessian e h p r t z)) (x-z)

/-- A certificate of actual full-space scalar-function source properties.
Every field is proved from the genuine construction in the theorem below.
Article: main_krylov, prop:Fcycle(iii). -/
def HilbertPlaneTrueMetricRealization (e h m : EuclideanSpace ℝ (Fin n))
    (p r a : ℝ) (t : krylov.Tensor.BinaryCubic) (z : EuclideanSpace ℝ (Fin n)) : Prop :=
  gradient (hilbertPlaneObjective e h m p r t) z=0 ∧
  let b := physicalOperatorMatrix (hilbertPlaneHessian e h p r t z)
  ∃ hb : b.PosDef,
    cgOperator b=fderiv ℝ (gradient (hilbertPlaneObjective e h m p r t)) z ∧
    (∀ v : EuclideanSpace ℝ (Fin n), |t.tensor.form (hilbertPlaneProject e h v)
      (hilbertPlaneProject e h v) (hilbertPlaneProject e h v)|≤2*a*‖metricCoordinates b hb v‖^3) ∧
    IsStandardSelfConcordantOn (hilbertPlaneObjective e h m p r t)
      {y | ‖metricCoordinates b hb (y-z)‖<canonicalCubicRadius a} ∧
    IsMinOn (hilbertPlaneObjective e h m p r t)
      {y | ‖metricCoordinates b hb (y-z)‖<canonicalCubicRadius a} z

set_option maxHeartbeats 1000000 in
/-- Every attained planar information chord lifts to genuine full-dimensional
self-concordant sources with the sharp actual error coefficient, uniformly
before every unrestricted common output and orthogonal quadratic centre.
Article: main_krylov, prop:Fcycle(iii). -/
theorem hilbertPlane_sharp_true_metric_sources
    (e h : EuclideanSpace ℝ (Fin n)) (he : ‖e‖=1) (hh : ‖h‖=1) (heh : inner ℝ e h=0)
    (r a : ℝ) (hr : 0<r) (ha : 0<a) (ha₁ : a<1) :
    ∃ t u : krylov.Tensor.BinaryCubic, Chord r t u ∧ chordValue r t u=fibreMinimax r ∧
    ∃ ε₀ C M E : ℝ, 0<ε₀ ∧ 0<C ∧ 0<M ∧ 0<E ∧
      ∀ p : ℝ, 0<p → p<ε₀ → ∀ m : EuclideanSpace ℝ (Fin n), hilbertPlaneProject e h m=0 →
      let α := 2*a*(1-C*p)^3
      0<α ∧ α≤2*a ∧ observe r (scaleBinaryCubic α t)=observe r (scaleBinaryCubic α u) ∧
      ∃ z w : Plane,
        ‖z-planeOfPair (p,r*p)‖≤M*p^2 ∧ ‖w-planeOfPair (p,r*p)‖≤M*p^2 ∧
        let zf := hilbertPlaneEmbed e h z+m
        let wf := hilbertPlaneEmbed e h w+m
        HilbertPlaneTrueMetricRealization e h m p r a (scaleBinaryCubic α t) zf ∧
        HilbertPlaneTrueMetricRealization e h m p r a (scaleBinaryCubic α u) wf ∧
        ‖hilbertPlaneHessian e h p r (scaleBinaryCubic α t) zf-ContinuousLinearMap.id ℝ _‖≤C*p ∧
        ‖hilbertPlaneHessian e h p r (scaleBinaryCubic α u) wf-ContinuousLinearMap.id ℝ _‖≤C*p ∧
        ∀ x : EuclideanSpace ℝ (Fin n),
          a^2*r^2*Real.sqrt (1+4*r^2)*fibreMinimax r*p^3-E*p^4≤
            max (hilbertPlaneMetricError e h p r (scaleBinaryCubic α t) zf x)
              (hilbertPlaneMetricError e h p r (scaleBinaryCubic α u) wf x) := by
  obtain ⟨t,u,hch,hatt,ep,C,M,E,hep,hC,hM,hE,hsource⟩ := planeCubic_sharp_true_metric_sources r a hr ha ha₁
  let K := a^2*r^2*Real.sqrt (1+4*r^2)*fibreMinimax r
  have hMF := (fibreMinimax_bounds r).1
  have hK : 0≤K := by dsimp only [K]; positivity
  refine ⟨t,u,hch,hatt,min ep (min 1 (1/(2*C+1))),C,M,E+C*K+2*K^2+1,
    by positivity,hC,hM,by positivity,?_⟩
  intro p hp heps m hm
  obtain ⟨hα,hαU,hobs,z,w,hz,hw,hHz,hHw,hzt,hwu,hlower⟩ := hsource p hp (heps.trans_le (min_le_left _ _))
  let α := 2*a*(1-C*p)^3
  let τ := scaleBinaryCubic α t
  let υ := scaleBinaryCubic α u
  let zf := hilbertPlaneEmbed e h z+m
  let wf := hilbertPlaneEmbed e h w+m
  have hztf : HilbertPlaneTrueMetricRealization e h m p r a τ zf :=
    hilbertPlane_true_metric_realization e h m he hh heh hm p r a α ha t z hzt
  have hwuf : HilbertPlaneTrueMetricRealization e h m p r a υ wf :=
    hilbertPlane_true_metric_realization e h m he hh heh hm p r a α ha u w hwu
  have hPz : hilbertPlaneProject e h zf=z := by
    dsimp only [zf]; rw [map_add,hilbertPlaneProject_embed e h he hh heh,hm,add_zero]
  have hPw : hilbertPlaneProject e h wf=w := by
    dsimp only [wf]; rw [map_add,hilbertPlaneProject_embed e h he hh heh,hm,add_zero]
  have hdz : ‖hilbertPlaneHessian e h p r τ zf-ContinuousLinearMap.id ℝ _‖≤C*p := by
    have hb := hilbertPlaneHessian_drift_norm e h he hh heh p r τ zf
    rw [hPz] at hb
    exact hb.trans hHz
  have hdw : ‖hilbertPlaneHessian e h p r υ wf-ContinuousLinearMap.id ℝ _‖≤C*p := by
    have hb := hilbertPlaneHessian_drift_norm e h he hh heh p r υ wf
    rw [hPw] at hb
    exact hb.trans hHw
  refine ⟨hα,hαU,hobs,z,w,hz,hw,hztf,hwuf,hdz,hdw,?_⟩
  intro x
  have hp1 : p≤1 := heps.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hCp : C*p≤1/2 := by
    have hc := (lt_div_iff₀ (by positivity : 0<2*C+1)).mp
      (heps.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    nlinarith only [hc,hp]
  have hα2 : α≤2 := hαU.trans (by linarith only [ha₁])
  have hgBound (s : krylov.Tensor.BinaryCubic) (hs : s.InBall) (zs : EuclideanSpace ℝ (Fin n))
      (hreal : HilbertPlaneTrueMetricRealization e h m p r a (scaleBinaryCubic α s) zs)
      (hds : ‖hilbertPlaneHessian e h p r (scaleBinaryCubic α s) zs-ContinuousLinearMap.id ℝ _‖≤C*p) :
      ‖gradient (hilbertPlaneObjective e h m p r (scaleBinaryCubic α s)) x‖≤
        (1+C*p)*hilbertPlaneMetricError e h p r (scaleBinaryCubic α s) zs x+
          2*(hilbertPlaneMetricError e h p r (scaleBinaryCubic α s) zs x)^2 := by
    obtain ⟨hc,hb,_,_,_,_⟩ := hreal
    let b := physicalOperatorMatrix (hilbertPlaneHessian e h p r (scaleBinaryCubic α s) zs)
    have hglobal := hilbertPlaneHessian_lipschitz e h he hh heh p r α hα.le hs
    have hg := trueMetric_gradient_bound _ _
      (fun y=>hilbertPlaneGradient_hasFDerivAt e h m p r (scaleBinaryCubic α s) y) hglobal zs hc b hb
      (physicalOperatorMatrix_operator _).symm (by positivity : 0≤C*p) hCp hds x
    rw [←referenceMetricSize_eq_norm b hb,Real.coe_toNNReal _ hα.le] at hg
    exact hg.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hα2 (sq_nonneg _)))
  have hg0 := hgBound t hch.1 zf hztf hdz
  have hg1 := hgBound u hch.2.1 wf hwuf hdw
  have hgradLower : K*p^3-E*p^4≤
      max ‖gradient (hilbertPlaneObjective e h m p r τ) x‖
        ‖gradient (hilbertPlaneObjective e h m p r υ) x‖ :=
    (hlower (hilbertPlaneProject e h x)).trans (max_le_max
      (hilbertPlaneGradient_norm_lower e h m he hh heh hm p r τ x)
      (hilbertPlaneGradient_norm_lower e h m he hh heh hm p r υ x))
  have herror := two_source_metric_error_lower hK hE.le hC.le (by norm_num : (0:ℝ)≤2) hp.le hp1
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hgradLower hg0 hg1
  exact (sub_le_sub_left (mul_le_mul_of_nonneg_right (by linarith : E+C*K+2*K^2≤E+C*K+2*K^2+1)
    (pow_nonneg hp.le 4)) _).trans herror

end
end krylov.Functions
