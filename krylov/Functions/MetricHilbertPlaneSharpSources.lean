import krylov.Functions.HilbertPlaneSharpSources
import krylov.Functions.GenericMetricPullback
import krylov.Functions.MetricHilbertPlane

/-!
Article: main_krylov, prop:Fcycle(iii), actual physical sharp cubic sources.
Use: retain any prescribed positive reference matrix while pulling the full
scalar information fibre into physical coordinates. True errors, exact tensor
budgets and the complete true-minimizer SC balls are preserved exactly.
Source: actual full-space construction and the proved positive-root pullback.
-/
namespace krylov.Functions
noncomputable section
open Set Matrix krylov.Tensor.BinaryCubic krylov.Nonlinear krylov.Reference krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual physical true-minimizer Hessian of a lifted scalar source.
Article: main_krylov, prop:Fcycle(iii). -/
def metricHilbertPlaneTrueHessian (base : Matrix (Fin n) (Fin n) ℝ)
    (e h : EuclideanSpace ℝ (Fin n)) (p r : ℝ) (t : krylov.Tensor.BinaryCubic)
    (z : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  metricRoot base*physicalOperatorMatrix (hilbertPlaneHessian e h p r t z)*metricRoot base

/-- Actual error in the true physical minimizer Hessian.
Article: main_krylov, prop:Fcycle(iii). -/
def metricHilbertPlaneMetricError (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (e h : EuclideanSpace ℝ (Fin n)) (p r : ℝ) (t : krylov.Tensor.BinaryCubic)
    (z x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  referenceMetricSize (metricHilbertPlaneTrueHessian base e h p r t z)
    (x-(metricCoordinates base hb).symm z)

/-- A physical realization certificate whose entries are actual scalar
function properties, with the true positive Hessian and complete metric ball.
Article: main_krylov, prop:Fcycle(iii). -/
def MetricHilbertPlaneTrueMetricRealization (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (e h m : EuclideanSpace ℝ (Fin n)) (p r a : ℝ) (t : krylov.Tensor.BinaryCubic)
    (z : EuclideanSpace ℝ (Fin n)) : Prop :=
  let S := metricCoordinates base hb
  let f := metricHilbertPlaneObjective S e h m p r t
  let y := S.symm z
  let P := metricHilbertPlaneTrueHessian base e h p r t z
  gradient f y=0 ∧ ∃ hP : P.PosDef,
    cgOperator P=fderiv ℝ (gradient f) y ∧
    (∀ v : EuclideanSpace ℝ (Fin n), |t.tensor.form (hilbertPlaneProject e h (S v))
      (hilbertPlaneProject e h (S v)) (hilbertPlaneProject e h (S v))|≤2*a*‖metricCoordinates P hP v‖^3) ∧
    IsStandardSelfConcordantOn f {x | ‖metricCoordinates P hP (x-y)‖<canonicalCubicRadius a} ∧
    IsMinOn f {x | ‖metricCoordinates P hP (x-y)‖<canonicalCubicRadius a} y

/-- All actual full-space source properties survive the true physical
positive-root change, without changing radius or tensor budget.
Article: main_krylov, prop:Fcycle(iii). -/
theorem metricHilbertPlane_true_metric_realization
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (e h m : EuclideanSpace ℝ (Fin n)) (p r a : ℝ) (ha : 0<a) (ha₁ : a<1)
    (t : krylov.Tensor.BinaryCubic) (z : EuclideanSpace ℝ (Fin n))
    (hreal : HilbertPlaneTrueMetricRealization e h m p r a t z) :
    MetricHilbertPlaneTrueMetricRealization base hb e h m p r a t z := by
  obtain ⟨hc,hb',hder,hbudget,hSC,hmin⟩ := hreal
  exact metricPullback_true_metric_realization base _ hb hb' (hilbertPlaneObjective e h m p r t) z
    (canonicalCubicRadius a) (2*a) (canonicalCubicRadius_pos ha ha₁)
    (fun v=>t.tensor.form (hilbertPlaneProject e h v) (hilbertPlaneProject e h v) (hilbertPlaneProject e h v))
    hc hder hbudget hSC hmin

/-- The actual physical true-Hessian error equals the actual full canonical
true-Hessian error exactly. Article: main_krylov, prop:Fcycle(iii). -/
theorem metricHilbertPlaneMetricError_eq
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (e h : EuclideanSpace ℝ (Fin n)) (p r : ℝ) (t : krylov.Tensor.BinaryCubic)
    (z x : EuclideanSpace ℝ (Fin n))
    (hb' : (physicalOperatorMatrix (hilbertPlaneHessian e h p r t z)).PosDef) :
    metricHilbertPlaneMetricError base hb e h p r t z x=
      hilbertPlaneMetricError e h p r t z (metricCoordinates base hb x) := by
  let b := physicalOperatorMatrix (hilbertPlaneHessian e h p r t z)
  have hP := metricPullbackMatrix_posDef base b hb hb'
  dsimp only [metricHilbertPlaneMetricError,metricHilbertPlaneTrueHessian,hilbertPlaneMetricError]
  rw [referenceMetricSize_eq_norm _ hP,referenceMetricSize_eq_norm _ hb',
    metricPullback_true_metric_norm base b hb hb' hP,map_sub,(metricCoordinates base hb).apply_symm_apply]

/-- The actual physical common-output lower bound uses the genuine
true-minimizer metric of each indistinguishable scalar function.
Article: main_krylov, prop:Fcycle(iii), physical sharpness transfer. -/
theorem metricHilbertPlane_common_error_lower
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (e h m : EuclideanSpace ℝ (Fin n)) (p r a : ℝ) (t u : krylov.Tensor.BinaryCubic)
    (z w : EuclideanSpace ℝ (Fin n)) (ht : HilbertPlaneTrueMetricRealization e h m p r a t z)
    (hu : HilbertPlaneTrueMetricRealization e h m p r a u w)
    (L : ℝ) (hlower : ∀ x : EuclideanSpace ℝ (Fin n), L≤
      max (hilbertPlaneMetricError e h p r t z x) (hilbertPlaneMetricError e h p r u w x)) :
    ∀ x : EuclideanSpace ℝ (Fin n), L≤
      max (metricHilbertPlaneMetricError base hb e h p r t z x)
        (metricHilbertPlaneMetricError base hb e h p r u w x) := by
  obtain ⟨_,hbt,_,_,_,_⟩ := ht
  obtain ⟨_,hbu,_,_,_,_⟩ := hu
  intro x
  rw [metricHilbertPlaneMetricError_eq base hb e h p r t z x hbt,
    metricHilbertPlaneMetricError_eq base hb e h p r u w x hbu]
  exact hlower _

end
end krylov.Functions
