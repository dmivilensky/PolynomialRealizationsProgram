import polyak.Boundary.P2.Rational
import polyak.Numerics.Parametric.Scale

/-!
Exact shifted divided polynomial codes. Every coefficient identity is checked
against the independent source; the regularized expression remains valid at zero.
-/
namespace polyak.Numerics
open LeanCert.Core LeanCert.Engine Polynomial

def polynomialExpr (p : QPoly) (arg : Expr) : Expr := Parametric.substitute (fun _ => arg) p.toExpr

noncomputable section

theorem polynomialExpr_value (p : QPoly) (arg : Expr) (ρ : ℕ → ℝ) :
    Expr.eval ρ (polynomialExpr p arg)=aeval (Expr.eval ρ arg) p.toPoly := by
  rw [polynomialExpr,Parametric.substitute_eval]
  exact QPoly.eval_toExpr p (Expr.eval ρ arg)

/-- Shift and remove the constant term by a checked polynomial identity. -/
theorem shifted_divided_exact {f : ℝ → ℝ} (p : QPoly)
    (hf : ∀ x : ℝ, aeval x p.toPoly=f x) (a b : ℚ) (q : QPoly)
    (hc : Boundary.P2.polynomialCheck (p.compose ((QPoly.constant a).add QPoly.X))
      ((QPoly.constant b).add (QPoly.X.mul q))=true) (x : ℝ) :
    f ((a : ℝ)+x)=(b : ℝ)+x*aeval x q.toPoly := by
  have he := congrArg (aeval x) (Boundary.P2.polynomialCheck_sound hc)
  simp only [QPoly.aeval_compose,QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,
    QPoly.toPoly_X,map_add,map_mul,aeval_C,aeval_X,hf] at he
  exact he

/-- The unscaled shifted polynomial also retains its exact source. -/
theorem shifted_exact {f : ℝ → ℝ} (p : QPoly)
    (hf : ∀ x : ℝ, aeval x p.toPoly=f x) (a : ℚ) (q : QPoly)
    (hc : Boundary.P2.polynomialCheck (p.compose ((QPoly.constant a).add QPoly.X)) q=true)
    (x : ℝ) : aeval x q.toPoly=f ((a : ℝ)+x) := by
  have he := congrArg (aeval x) (Boundary.P2.polynomialCheck_sound hc)
  simp only [QPoly.aeval_compose,QPoly.toPoly_add,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,aeval_C,aeval_X,hf] at he
  exact he.symm

end
end polyak.Numerics
