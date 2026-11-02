import krylov.Convergence.OneGradientCubicMetric

/-!
Article: main_krylov, thm:LB, genuine polynomial and canonical tensor.
Use: identify the actual scalar fibre objectives, their real Riesz
gradients/Hessians/third derivatives and the exact canonical rank-one
cubic tensor with its attained diagonal budget.
Source: polynomial differentiation and the true SPD root pairing.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set krylov.Methods krylov.Reference krylov.Functions krylov.OneGradient krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The actual scalar fibre objective, retaining both hidden parameters.
Article: main_krylov, thm:LB, f_(b,t). -/
def oneGradientCubicFibreObjective (base : Matrix (Fin n) (Fin n) ℝ) (g a : E) (b t : ℝ) : E → ℝ :=
  oneGradientCubicObjective (cgOperator base+b • InnerProductSpace.rankOne ℝ a a) g a t

/-- Both true fibre curvatures are self-adjoint, including parameters
of either sign; positive definiteness is treated separately.
Article: main_krylov, thm:LB. -/
theorem oneGradientCubicFibre_symmetric
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (a : E) (b : ℝ) :
    (cgOperator base+b • InnerProductSpace.rankOne ℝ a a).toLinearMap.IsSymmetric := by
  intro u v
  have hQ := (cgOperator_positive base hb).1 u v
  change inner ℝ (cgOperator base u) v=inner ℝ u (cgOperator base v) at hQ
  change inner ℝ ((cgOperator base+b • InnerProductSpace.rankOne ℝ a a) u) v=
    inner ℝ u ((cgOperator base+b • InnerProductSpace.rankOne ℝ a a) v)
  simp only [_root_.add_apply,_root_.smul_apply,InnerProductSpace.rankOne_apply,
    inner_add_left,inner_add_right,real_inner_smul_left,inner_smul_right,smul_smul]
  rw [hQ,real_inner_comm a u]
  ring

/-- The actual nonlinear oracle used in the indistinguishability proof
is the true derivative of this literal scalar polynomial.
Article: main_krylov, thm:LB. -/
theorem oneGradientCubicFibreObjective_hasFDerivAt
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g a : E) (b t : ℝ) (x : E) :
    HasFDerivAt (oneGradientCubicFibreObjective base g a b t)
      (innerSL ℝ (oneGradientCubicFibreGradient (cgOperator base) g a b t x)) x :=
  oneGradientCubicObjective_hasFDerivAt _ (oneGradientCubicFibre_symmetric base hb a b) g a t x

/-- Every genuine fibre objective is smooth to every finite order.
Article: main_krylov, thm:LB. -/
theorem oneGradientCubicFibreObjective_contDiff
    (base : Matrix (Fin n) (Fin n) ℝ) (g a : E) (b t : ℝ) (r : ℕ) :
    ContDiff ℝ r (oneGradientCubicFibreObjective base g a b t) :=
  oneGradientCubicObjective_contDiff _ g a t r

/-- The actual canonical third tensor of the physical rank-one cubic
has dual axis A^(-1/2)a. This exact identity fixes all normalization
factors in the original lower bound. Article: thm:LB. -/
theorem oneGradientCubicThird_canonical_pair
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (a : E) (t : ℝ) (u v w : E) :
    (rankOneCubic (cgOperator (metricRoot base)⁻¹ a) t).form
      (cgOperator (metricRoot base) u) (cgOperator (metricRoot base) v)
      (cgOperator (metricRoot base) w)=inner ℝ (oneGradientCubicThird a t u v) w := by
  have hp (x : E) : inner ℝ (cgOperator (metricRoot base)⁻¹ a) (cgOperator (metricRoot base) x)=inner ℝ a x := by
    have hh := oneGradient_hidden_metric_pairing base hb a x
    change inner ℝ a x=inner ℝ (cgOperator (metricRoot base)⁻¹ a)
      (Matrix.toEuclideanCLM (𝕜:=ℝ) (metricRoot base)⁻¹ (cgOperator base x)) at hh
    rw [canonical_reference_action base hb] at hh
    exact hh.symm
  rw [rankOneCubic_apply,oneGradientCubicThird_pair,rankOneCubic_apply,hp,hp,hp]

/-- The genuine canonical cubic obeys its exact original diagonal
budget, with no auxiliary mixed-norm hypothesis. Article: thm:LB. -/
theorem oneGradientCubicThird_canonical_bound
    (base : Matrix (Fin n) (Fin n) ℝ) (a : E) (t : ℝ) (v : E) (hv : ‖v‖=1) :
    |(rankOneCubic (cgOperator (metricRoot base)⁻¹ a) t).form v v v|≤
      |t| *‖cgOperator (metricRoot base)⁻¹ a‖^3 :=
  rankOneCubic_diagonal_bound _ t v hv

end
end krylov.Convergence
