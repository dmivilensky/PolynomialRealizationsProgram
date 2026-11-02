import krylov.OneGradient.TwoQueryRiskAttainment
import krylov.Methods.OneGradientCoordinates
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(c), exact physical arbitrary-query coordinates.
Use: genuine canonical hidden matrices act on actual original M1 queries
and produce the real incoming residuals used by the finite lower game.
Source: true first-prefix causality and actual positive-root form transport.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Methods krylov.Reference krylov.Secant krylov.Information

/-- The actual incoming gradient on a prescribed physical second form
has its exact canonical arbitrary-query coordinates. Both real queries
are those selected before the unknown second operator is observed.
Use: the four genuine adversarial residuals retain the actual reference
mismatch and query length, without replacing the competitor by CG.
Article: main_krylov, thm:local(c), exact arbitrary-query residual dictionary.
Proof: expand the two true evaluated gradient updates. Their first history
is independent of the second segment. The actual canonical reference
action and inverse-root form action give the two exact coordinate terms. -/
theorem twoQuery_physical_form_gradient
    {n : ℕ} (base J : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (m : OneGradientMethod (EuclideanSpace ℝ (Fin n))) (g : EuclideanSpace ℝ (Fin n)) :
    let R := cgOperator (metricRoot base)
    let C := inverseFormMap (metricRoot base)⁻¹ J
    let H := oneGradientRun m (twoQueryOperators (cgOperator base) (cgOperator C)) g 2
    cgOperator (metricRoot base)⁻¹ H.gradient=
      cgOperator (metricRoot base)⁻¹ g+
        R (oneGradientStep m (fun _ => cgOperator base) g 0)+
        cgOperator J (R (oneGradientStep m (fun _ => cgOperator base) g 1)) := by
  dsimp only
  change cgOperator (metricRoot base)⁻¹
    ((g+cgOperator base (oneGradientStep m (fun _ => cgOperator base) g 0))+
      cgOperator (inverseFormMap (metricRoot base)⁻¹ J)
        (oneGradientStep m (fun _ => cgOperator base) g 1))=_
  have href (u : EuclideanSpace ℝ (Fin n)) : cgOperator (metricRoot base)⁻¹ (cgOperator base u)=
      cgOperator (metricRoot base) u := canonical_reference_action base hb u
  rw [map_add,map_add,href,inverseRootForm_action base J hb]

/-- A true hidden canonical form annihilating the actual canonical query
has zero action on that genuine query after physical transport as well.
Use: complete original hidden-pair histories are exactly identical.
Article: main_krylov, thm:local(c), true physical hidden-query annihilator.
Proof: the inverse-root physical form is the positive-root congruence;
the right root preserves the true query and the left root maps zero to zero. -/
theorem twoQuery_physical_hidden_action
    {n : ℕ} (base D : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (u : EuclideanSpace ℝ (Fin n)) (hD : cgOperator D (cgOperator (metricRoot base) u)=0) :
    cgOperator (inverseFormMap (metricRoot base)⁻¹ D) u=0 := by
  rw [inverseRootForm base D hb]
  simp only [cgOperator,map_mul,mul_apply_eq_comp]
  change cgOperator (metricRoot base) (cgOperator D (cgOperator (metricRoot base) u))=0
  rw [hD,map_zero]

end
end krylov.OneGradient
