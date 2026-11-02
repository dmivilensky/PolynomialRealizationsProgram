import krylov.Convergence.OneGradientCubicTwins
import krylov.Convergence.OneGradientLowerScalar
import krylov.Reference.CanonicalGradient

/-!
Article: main_krylov, thm:LB, actual opposite-cubic output lower bound.
Use: bound the true inverse-root gradient at every possible common output
of the genuine indistinguishable polynomial sources. The original policy
is arbitrary, and no localization or boundedness of its output is assumed.
Source: Appendix G's opposite-sign argument, exact metric duality and
Cauchy--Schwarz; all scalar-source transcripts are actual executions.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set krylov.Methods krylov.Reference krylov.Functions krylov.OneGradient krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The hidden physical coordinate is exactly paired with the true dual
metric gradient; no condition-number estimate is substituted.
Article: main_krylov, thm:LB, hidden-coordinate control. -/
theorem oneGradient_hidden_metric_pairing
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (a x : E) :
    inner ℝ a x=inner ℝ (cgOperator (metricRoot base)⁻¹ a)
      (cgOperator (metricRoot base)⁻¹ (cgOperator base x)) := by
  change inner ℝ a x=inner ℝ (Matrix.toEuclideanCLM (𝕜:=ℝ) (metricRoot base)⁻¹ a)
    (Matrix.toEuclideanCLM (𝕜:=ℝ) (metricRoot base)⁻¹ (cgOperator base x))
  rw [canonical_reference_action base hb]
  exact (real_inner_comm _ _).trans ((canonical_search_pairing base hb x a).trans (real_inner_comm _ _))

/-- Every real output coordinate is controlled by its actual quadratic
metric residual, not by an assumed output-size bound. Article: thm:LB. -/
theorem oneGradient_hidden_metric_coordinate
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g a x₀ y : E)
    (hx₀ : g+cgOperator base x₀=0) :
    |inner ℝ a y-inner ℝ a x₀|≤‖cgOperator (metricRoot base)⁻¹ a‖*
      ‖cgOperator (metricRoot base)⁻¹ (g+cgOperator base y)‖ := by
  have hg : g= -cgOperator base x₀ := eq_neg_of_add_eq_zero_left hx₀
  rw [←inner_sub_right,oneGradient_hidden_metric_pairing base hb]
  simpa only [map_sub,hg,neg_add_eq_sub] using
    abs_real_inner_le_norm (cgOperator (metricRoot base)⁻¹ a)
      (cgOperator (metricRoot base)⁻¹ (cgOperator base (y-x₀)))

/-- The true physical twin gradients are exactly a common quadratic
residual plus/minus the missing rank-one polynomial. Article: thm:LB. -/
theorem oneGradientCubicTwins_gradient
    (Q : E →L[ℝ] E) (g a : E) (M p : ℝ) (y : E) (s : ℝ) :
    oneGradientCubicFibreGradient Q g a (-s*M*p/2) (s*M) y=
      g+Q y+s • ((M/2*inner ℝ a y*(inner ℝ a y-p)) • a) := by
  rw [oneGradientCubicFibreGradient_eq,smul_smul]
  congr 1
  congr 1
  ring

/-- The original opposite-cubic lower estimate holds at every common
output, with an explicit relative denominator tending to one on small
sources. This is a true scalar-function statement in the actual SPD
metric, and includes arbitrary remote outputs. Article: thm:LB. -/
theorem oneGradientCubicTwins_metric_output_lower
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g a x₀ y : E) (hx₀ : g+cgOperator base x₀=0) (M p : ℝ) (hM : 0≤M) :
    let R := cgOperator (metricRoot base)⁻¹
    let c := ‖R a‖
    let z₀ := inner ℝ a x₀
    let T := (M/2*c)*|z₀| *|z₀-p|
    let η := (M/2*c)*c*(|z₀|+|z₀-p|+c*T)
    T/(1+η)≤max
      ‖R (oneGradientCubicFibreGradient (cgOperator base) g a (-M*p/2) M y)‖
      ‖R (oneGradientCubicFibreGradient (cgOperator base) g a (M*p/2) (-M) y)‖ := by
  let R := cgOperator (metricRoot base)⁻¹
  let v := R (g+cgOperator base y)
  let w := R ((M/2*inner ℝ a y*(inner ℝ a y-p)) • a)
  have hp : R (oneGradientCubicFibreGradient (cgOperator base) g a (-M*p/2) M y)=v+w := by
    simpa only [v,w,neg_mul,one_mul,one_smul,map_add] using
      congrArg R (oneGradientCubicTwins_gradient (cgOperator base) g a M p y 1)
  have hm : R (oneGradientCubicFibreGradient (cgOperator base) g a (M*p/2) (-M) y)=v-w := by
    simpa only [v,w,neg_mul,one_mul,neg_neg,neg_smul,one_smul,map_add,map_neg,sub_eq_add_neg] using
      congrArg R (oneGradientCubicTwins_gradient (cgOperator base) g a M p y (-1))
  change _≤max ‖R (oneGradientCubicFibreGradient (cgOperator base) g a (-M*p/2) M y)‖
    ‖R (oneGradientCubicFibreGradient (cgOperator base) g a (M*p/2) (-M) y)‖
  rw [hp,hm]
  have hnorm : ‖w‖=(M/2*‖R a‖)*|inner ℝ a y| *|inner ℝ a y-p| := by
    dsimp only [w]
    rw [map_smul,norm_smul,Real.norm_eq_abs,abs_mul,abs_mul,abs_of_nonneg (by positivity : 0≤M/2)]
    ring
  have hvw := opposite_outputs_norm_lower v w
  have hcoordinate := (oneGradient_hidden_metric_coordinate base hb g a x₀ y hx₀).trans
    (mul_le_mul_of_nonneg_left hvw.1 (norm_nonneg (R a)))
  exact hidden_product_output_lower (M/2*‖R a‖) ‖R a‖ (max ‖v+w‖ ‖v-w‖)
    (inner ℝ a y) (inner ℝ a x₀) p (by positivity) (norm_nonneg _) (by positivity)
    (hnorm ▸ hvw.2) hcoordinate

end
end krylov.Convergence
