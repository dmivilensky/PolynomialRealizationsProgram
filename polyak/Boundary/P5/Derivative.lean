import polyak.Boundary.P5.PhysicalContinuation
import polyak.Boundary.P5.DerivativeContinuation
import polyak.Boundary.P5.DerivativeTransfer

/-! Article: actual central-boundary analyticity and strict derivative reserves,
including source-side derivatives at the exact P₂ junction. -/
namespace polyak.Boundary.P5
noncomputable section
open Spectral Set

private theorem actual_formula : ∀ h∈Icc (0 : ℝ) (P2.Ga-1),∀ t : ℝ,
    Real.cosh t=1+h → V t=Real.arsinh (continuationU h) := by
  intro h hh t ht
  exact continuation_optimal hh ht

theorem hasDerivWithinAt_V {t : ℝ} (hl : 1<Real.cosh t) (hu : Real.cosh t≤P2.Ga) :
    HasDerivWithinAt V (boundaryDerivative t) centralExponentArc t :=
  hasDerivWithinAt_of_branch V actual_formula hl hu

theorem abs_boundaryDerivative_lt_one {t : ℝ} (hl : 1<Real.cosh t)
    (hu : Real.cosh t≤P2.Ga) : |boundaryDerivative t|<1 :=
  abs_boundaryDerivative_lt_one_of_source
    (continuation_derivative_bounds (centralParameter_mem hl hu)).1 hl hu

theorem hasDerivAt_V {t : ℝ} (hl : 1<Real.cosh t) (hu : Real.cosh t<P2.Ga) :
    HasDerivAt V (boundaryDerivative t) t :=
  hasDerivAt_of_branch V actual_formula hl hu

theorem abs_deriv_V_lt_one {t : ℝ} (hl : 1<Real.cosh t) (hu : Real.cosh t<P2.Ga) :
    |deriv V t|<1 := by
  rw [(hasDerivAt_V hl hu).deriv]
  exact abs_boundaryDerivative_lt_one hl hu.le

theorem V_analyticAt {t : ℝ} (hl : 1<Real.cosh t) (hu : Real.cosh t<P2.Ga) :
    AnalyticAt ℝ V t :=
  analyticAt_of_branch V actual_formula hl hu

/-- The negative exact P₂ junction has its actual right derivative from P₅. -/
theorem hasDerivWithinAt_V_right {t : ℝ} (ht : t<0) (hu : Real.cosh t≤P2.Ga) :
    HasDerivWithinAt V (boundaryDerivative t) (Ici t) t :=
  hasDerivWithinAt_right_of_branch V actual_formula ht hu

end
end polyak.Boundary.P5
