import polyak.Numerics.ShiftedCode

/-! Exact expression graphs for proved univariate rational source representations. -/
namespace polyak.Boundary.P2
open LeanCert.Core LeanCert.Engine Numerics Polynomial

def RationalCode.expression {S : Set ℝ} {f : ℝ → ℝ} (code : RationalCode S f) : Expr :=
  .mul (polynomialExpr code.numerator (.var 0))
    (.inv (polynomialExpr code.denominator (.var 0)))

noncomputable section

theorem RationalCode.expression_eval {S : Set ℝ} {f : ℝ → ℝ} (code : RationalCode S f)
    (ρ : ℕ → ℝ) (hρ : ρ 0∈S) : Expr.eval ρ code.expression=f (ρ 0) := by
  simp only [expression,Expr.eval,polynomialExpr_value]
  exact (code.exact (ρ 0) hρ).symm

end
end polyak.Boundary.P2
