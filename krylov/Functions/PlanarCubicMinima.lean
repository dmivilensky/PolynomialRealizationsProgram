import krylov.Functions.PlanarHessianBounds

/-!
Article: main_krylov, prop:Fcycle(iii), true minimizers of cubic sources.
Use: certify that the stationary point is the actual minimizer throughout
its positive-Hessian domain. Source: the exact degree-three endpoint Hessian
Taylor formula, whose convex combination is positive at both endpoints.
-/
namespace krylov.Functions
noncomputable section
open Set Metric krylov.Tensor.BinaryCubic
open scoped InnerProductSpace

/-- The exact cubic value gap is its actual first differential plus the
one-third/one-sixth combination of the two genuine endpoint Hessians.
Article: main_krylov, prop:Fcycle(iii), true cubic minimizer certificate. -/
theorem planeCubicObjective_endpoint_identity (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (x y : Plane) :
    planeCubicObjective p r t y-planeCubicObjective p r t x-
      inner ℝ (gradient (planeCubicObjective p r t) x) (y-x)=
      (1/3:ℝ)*inner ℝ (y-x) (planeCubicHessian p r t x (y-x))+
        (1/6:ℝ)*inner ℝ (y-x) (planeCubicHessian p r t y (y-x)) := by
  rw [planeCubicGradient_actual]
  simp [planeCubicObjective,planarCubicObjective,planarReferenceQuadratic,planarValueFamily,
    planeCubicGradient,planarCubicGradient,planarValueCoordinateDerivative,planeCubicHessian,
    planeValueHessianOperator,planeOfPair,pairOfPlane,PiLp.inner_apply,Fin.sum_univ_two,
    ContinuousLinearMap.smulRight_apply]
  ring

/-- A genuine critical point minimizes the entire actual scalar cubic on
any domain with positive endpoint Hessians; the gap has its true uniform
quadratic lower bound. Article: main_krylov, prop:Fcycle(iii). -/
theorem planeCubicObjective_critical_gap (p r m : ℝ) (t : krylov.Tensor.BinaryCubic)
    (U : Set Plane) (x : Plane) (hx : x∈U)
    (hcritical : gradient (planeCubicObjective p r t) x=0)
    (hlower : ∀ z∈U, ∀ v : Plane, m*‖v‖^2≤ inner ℝ v (planeCubicHessian p r t z v)) :
    ∀ y∈U, m/2*‖y-x‖^2≤planeCubicObjective p r t y-planeCubicObjective p r t x := by
  intro y hy
  have hh := planeCubicObjective_endpoint_identity p r t x y
  rw [hcritical,inner_zero_left,sub_zero] at hh
  have h0 := hlower x hx (y-x)
  have h1 := hlower y hy (y-x)
  linarith only [hh,h0,h1]

/-- Positive true Hessians and true criticality give the actual minimizer,
without storing minimization as a source assumption.
Article: main_krylov, prop:Fcycle(iii). -/
theorem planeCubicObjective_isMinOn (p r m : ℝ) (hm : 0≤m) (t : krylov.Tensor.BinaryCubic)
    (U : Set Plane) (x : Plane) (hx : x∈U)
    (hcritical : gradient (planeCubicObjective p r t) x=0)
    (hlower : ∀ z∈U, ∀ v : Plane, m*‖v‖^2≤ inner ℝ v (planeCubicHessian p r t z v)) :
    IsMinOn (planeCubicObjective p r t) U x := by
  intro y hy
  have hh := planeCubicObjective_critical_gap p r m t U x hx hcritical hlower y hy
  have hn : 0≤m/2*‖y-x‖^2 := by positivity
  change planeCubicObjective p r t x≤planeCubicObjective p r t y
  exact sub_nonneg.mp (hn.trans hh)

end
end krylov.Functions
