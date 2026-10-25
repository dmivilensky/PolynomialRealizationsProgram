import polyak.Numerics.TensorBernstein
import polyak.Numerics.BivariateIdentity

/-! Tensor Bernstein expressions reflected by the exact bivariate polynomial engine. -/
noncomputable section
namespace polyak.Numerics.TensorBernstein
open BivariateIdentity

def Certificate.expression (c : Certificate) : Expr :=
  Expr.sum (List.ofFn fun i : Fin (c.degree0+1) =>
    Expr.sum (List.ofFn fun j : Fin (c.degree1+1) =>
      .mul (.mul (.mul (.mul (.literal (c.coefficient i j)) (.pow .x i))
        (.pow (.add (.literal 1) (.mul (.literal (-1)) .x)) (c.degree0-i))) (.pow .y j))
        (.pow (.add (.literal 1) (.mul (.literal (-1)) .y)) (c.degree1-j))))

theorem Certificate.expression_value (c : Certificate) (x y : ℝ) :
    c.expression.value x y=c.value x y := by
  simp only [Certificate.expression,Expr.sum_value,List.map_ofFn,List.sum_ofFn,Function.comp_apply,
    Expr.value,Certificate.value,basis,Rat.cast_one,Rat.cast_neg,neg_mul,one_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end polyak.Numerics.TensorBernstein
