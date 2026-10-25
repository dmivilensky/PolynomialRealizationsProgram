import polyak.Boundary.P1.Source
import polyak.Asymptotics.Taylor

/-!
Article: Appendix B, the regular one-atom blow-up at z=0.
Use: obtain an actual analytic branch and its local uniqueness from the source
polynomial system; its critical Jacobian is exactly four times the identity.
-/

namespace polyak.Boundary.P1
noncomputable section
open Filter
open scoped Topology ContDiff

/-- Article: the actual regularized equations are polynomial and hence analytic. -/
theorem regularSystem_contDiff : ContDiff ℝ ω regularSystem := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ω (fun p : ℝ×Coordinates => regularEquation0 p.1 (p.2 0) (p.2 1))
    unfold regularEquation0 uLinear gapLinear atomProductLinear contactQuadratic
    fun_prop
  · change ContDiff ℝ ω (fun p : ℝ×Coordinates => regularEquation1 p.1 (p.2 0) (p.2 1))
    unfold regularEquation1 gapLinear branchU
    fun_prop

/-- Article: the derivative in the two unknowns is the actual partial Jacobian 4I. -/
theorem regularSystem_partial_eq :
    fderiv ℝ regularSystem (0,criticalPoint) ∘L ContinuousLinearMap.inr ℝ ℝ Coordinates=
      (4 : ℝ) • ContinuousLinearMap.id ℝ Coordinates := by
  have hi : HasFDerivAt (fun Z : Coordinates => ((0 : ℝ),Z))
      (ContinuousLinearMap.inr ℝ ℝ Coordinates) criticalPoint :=
    (hasFDerivAt_const (𝕜:=ℝ) (c:=(0 : ℝ)) (x:=criticalPoint)).prodMk (hasFDerivAt_id _)
  have hcomp := regularSystem_contDiff.differentiable (by simp) |>.differentiableAt.hasFDerivAt
    |>.comp criticalPoint hi
  have hlin : HasFDerivAt (fun Z : Coordinates => (4 : ℝ) • Z+![-1/2,1])
      ((4 : ℝ) • ContinuousLinearMap.id ℝ Coordinates) criticalPoint :=
    ((hasFDerivAt_id criticalPoint).const_smul (4 : ℝ)).add_const ![-1/2,1]
  have he : (fun Z : Coordinates => regularSystem (0,Z))=
      (fun Z : Coordinates => (4 : ℝ) • Z+![-1/2,1]) := by
    funext Z
    rw [regularSystem_zero]
    ext i
    fin_cases i <;> simp
    ring
  change HasFDerivAt (fun Z : Coordinates => regularSystem (0,Z)) _ criticalPoint at hcomp
  rw [he] at hcomp
  exact hcomp.unique hlin

/-- Article: nonsingularity is proved for the actual unknown derivative. -/
theorem regularSystem_partial_isInvertible :
    (fderiv ℝ regularSystem (0,criticalPoint) ∘L
      ContinuousLinearMap.inr ℝ ℝ Coordinates).IsInvertible := by
  rw [regularSystem_partial_eq]
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g:=(1/4 : ℝ) • ContinuousLinearMap.id ℝ Coordinates)
  · ext v i
    norm_num
    ring
  · ext v i
    norm_num
    ring

/-- Article: the genuine analytic solution of the regular one-atom system. -/
def localBranch : ℝ → Coordinates :=
  regularSystem_contDiff.contDiffAt.implicitFunction (by simp) regularSystem_partial_isInvertible

theorem localBranch_zero : localBranch 0=criticalPoint :=
  regularSystem_contDiff.contDiffAt.implicitFunction_apply_self (by simp)
    regularSystem_partial_isInvertible

theorem localBranch_analyticAt : AnalyticAt ℝ localBranch 0 :=
  (regularSystem_contDiff.contDiffAt.contDiffAt_implicitFunction (by simp)
    regularSystem_partial_isInvertible).analyticAt

theorem localBranch_equations :
    ∀ᶠ z in 𝓝 (0 : ℝ),regularSystem (z,localBranch z)=0 := by
  simpa only [regularSystem_criticalPoint,localBranch] using
    regularSystem_contDiff.contDiffAt.eventually_apply_implicitFunction (by simp)
      regularSystem_partial_isInvertible

theorem localBranch_unique :
    ∀ᶠ p in 𝓝 ((0 : ℝ),criticalPoint),regularSystem p=0 ↔ localBranch p.1=p.2 := by
  simpa only [regularSystem_criticalPoint,localBranch] using
    regularSystem_contDiff.contDiffAt.eventually_apply_eq_iff_implicitFunction (by simp)
      regularSystem_partial_isInvertible

/-- Article: the source constants at the compactified endpoint are exactly 1/8 and −1/4. -/
theorem localBranch_initial : localBranch 0 0=1/8 ∧ localBranch 0 1= -1/4 := by
  rw [localBranch_zero]
  norm_num [criticalPoint]

end
end polyak.Boundary.P1
