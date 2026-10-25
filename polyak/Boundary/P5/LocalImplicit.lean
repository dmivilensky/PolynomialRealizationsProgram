import polyak.Boundary.P5.CriticalNonsingular
import polyak.Boundary.P5.CriticalSolution

/-!
Article: Theorem p5local, analytic implicit branch of the actual regularized system.
Use: the branch and its local uniqueness follow from the exact critical solution
and the actual invertible Frechet derivative, without an assumed branch certificate.
-/
noncomputable section
namespace polyak.Boundary.P5
open Filter
open scoped ContDiff Topology

/-- Article: analyticity of the actual source system in the analytic differentiability scale. -/
theorem regularSystem_contDiffAt :
    ContDiffAt ℝ ω regularSystem (0,criticalPoint) :=
  (regularSystem_analyticAt (0,criticalPoint)).contDiffAt

/-- Article: the actual analytic implicit branch in the original blown-up coordinates. -/
def localBranch : ℝ → Coordinates :=
  regularSystem_contDiffAt.implicitFunction (by simp) regularSystem_partial_isInvertible

/-- Article: the implicit branch passes through the exact algebraic critical point. -/
theorem localBranch_zero : localBranch 0=criticalPoint :=
  regularSystem_contDiffAt.implicitFunction_apply_self (by simp)
    regularSystem_partial_isInvertible

/-- Article: the implicit branch is real analytic at the singular parameter h=0. -/
theorem localBranch_analyticAt : AnalyticAt ℝ localBranch 0 :=
  (regularSystem_contDiffAt.contDiffAt_implicitFunction (by simp)
    regularSystem_partial_isInvertible).analyticAt

/-- Article: the analytic branch solves the seven actual regularized source equations. -/
theorem localBranch_equations :
    ∀ᶠ h in 𝓝 (0 : ℝ), regularSystem (h,localBranch h)=0 := by
  simpa only [regularSystem_criticalPoint,localBranch] using
    regularSystem_contDiffAt.eventually_apply_implicitFunction (by simp)
      regularSystem_partial_isInvertible

/-- Article: local uniqueness is for the actual source system and all seven original unknowns. -/
theorem localBranch_unique :
    ∀ᶠ p in 𝓝 ((0 : ℝ),criticalPoint),
      regularSystem p=0 ↔ localBranch p.1=p.2 := by
  simpa only [regularSystem_criticalPoint,localBranch] using
    regularSystem_contDiffAt.eventually_apply_eq_iff_implicitFunction (by simp)
      regularSystem_partial_isInvertible

end polyak.Boundary.P5
